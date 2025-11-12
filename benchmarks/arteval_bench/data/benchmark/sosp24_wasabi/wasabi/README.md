## 1. Overview

The testing component of WASABI triggers retry bugs by using a combination of static analysis, large language models (LLMs), fault injection, and testing. 

## 2. Getting Started

To get started, users should create a new directory structure, clone this repository, work on the `main` branch of the repository, configure and install dependencies, by following these steps:

1. Create a new workspace directory and clone the WASABI repository:
```bash
mkdir -p ~/wasabi-workspace/benchmarks
cd ~/wasabi-workspace/
git clone https://github.com/bastoica/wasabi
```

The working directory structure should look similar to the one below:
```plaintext
~/wasabi-workspace
  ├── benchmarks/
  └── wasabi/
      ├── LICENSE
      ├── README.md
      ├── wasabi-static/
      │   ├── README.md
      │   ├── codeql-if-detection
      │   ├── gpt-when-detection
      |   ├── retry_issue_set_artifact.xlsx
      |   └── wasabi_gpt_detection_results--table4.xlsx
      └── wasabi-testing
          ├── README.md
          ├── config/
          ├── pom-java11.xml
          ├── pom-java8.xml
          ├── pom.xml
          ├── src/
          └── utils/
```
The `wasabi` directory contains the codebase of WASABI, while the `bugfinding` directory is where users can add applications that they want to use WASABI to find retry bugs.

2. Set up the `WASABI_ROOT_DIR` environment variable:
```
export WASABI_ROOT_DIR=$(echo $HOME)/wasabi-workspace/wasabi
```
3. Installing necessary dependnecies:
```
cd ~/wasabi-workspace/wasabi/wasabi-testing/utils
sudo ./prereqs.sh
```

> [!NOTE]
> WASABI requires the following dependencies:
> * Ubuntu >=22.04 LTE
> * Python >=3.10
> * Java 8 and 11
> * Maven >=3.6
> * Gradle >=4.4.1
> * Ant >=1.10
> * AspectJ runtime plugin** (`aspectjr`) 1.9.8.M1 for Java 8 and 1.9.19 for Java 11, respectively
> * AspectJ Maven plugin** (`aspectj-maven-plugin`) 1.13 for Java 8 and 1.13.1 for Java 11, respectively
>
>**both added to WASABI's `pom.xml` as plugin dependencies
> 
> WASABI was developed, built, and tested on a bare metal machine with an Intel i7-8700 CPU, 32 GB of RAM, and 512 GB of disk space, running Ubuntu 22.04 LTE.
> While we implement WASABI to be agnostic to environment settings (i.e., OS distribution, versions of packages and dependencies), using WASABI in a different environment. Please see "[Known issues](README.md#7-known-issues)".

## 3. Building and installing WASABI

To build and install WASABI, first switch to the appropriate Java distribution. In this tutorial we work with Java 8 as it is the latest distribution required for HDFS.
```bash
sudo update-alternatives --config java 
...(select java 8)
export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64/jre
```

Next, run Maven's `clean`, `compile`, and `install` Maven from the `wasabi-testing` directory, to build WASABI. Note that the current codebase includes AspectJ for each of the applications used to evaluate WASABI (see Section 4 from our [paper](https://bastoica.github.io/files/papers/2024_sosp_wasabi.pdf)). In this walkthrough we build WASABI for finding bugs in HDFS (Hadoop) and use triggering HDFS-17590 as an example, [below](README.md#6-running-example-reproducing-hdfs-17590). 
```bash
cd ~/wasabi-workspace/wasabi/wasabi-testing
mvn clean install -U -fn -B -Dinstrumentation.target=hadoop -DskipTests 2>&1 | tee wasabi-install.log
```

If successful users should see a message similar to 
```bash
...
[INFO] ------------------------------------------------------------------------
[INFO] BUILD SUCCESS
[INFO] ------------------------------------------------------------------------
[INFO] Total time:  36.384 s
[INFO] Finished at: 2024-08-12T19:57:24Z
[INFO] ------------------------------------------------------------------------
```
If users need to use Java 11, they can either modify the `pom.xml` accordingly. We also provide pre-configured `pom` files for [Java 8](pom-java8.xml) and [Java 11](pom-java11.xml`).

> [!NOTE]
> When building WASABI multiple times, especially under a different Java distribution, it is recommended to first remove Maven's cache directory prior to compiling WASABI.
```bash
rm -rf ~/.m2/repository
```

## 4. Weaving (instrumenting) a target application

WASABI can be woven into or instrument a target applications either at compile- or load-time.

### 4.1 Compile-time weaving (Maven)

To enable compile-time weaving for a target application, users need to modify the original `pom.xml` of the target to include Wasabi as a dependence and invoke the `aspectj` plugin:

```xml
<dependencies>
  <!-- Existing dependencies -->

  <!-- AspectJ Runtime -->
  <dependency>
    <groupId>org.aspectj</groupId>
    <artifactId>aspectjrt</artifactId>
    <version>${aspectj.version}</version>
  </dependency>

  <!-- WASABI Fault Injection Library -->
  <dependency>
    <groupId>edu.uchicago.cs.systems</groupId>
    <artifactId>wasabi</artifactId>
    <version>${wasabi.version}</version>
  </dependency>
</dependencies>

<properties>
  <!-- Versions -->
  <aspectj.version>1.9.19</aspectj.version>
  <aspectj-maven.version>1.13.1</aspectj-maven.version>
  <wasabi.version>1.0.0</wasabi.version>
</properties>

<build>
  <plugins>
    <!-- Existing plugins -->

    <!-- AspectJ Maven Plugin -->
    <plugin>
      <groupId>dev.aspectj</groupId>
      <artifactId>aspectj-maven-plugin</artifactId>
      <version>${aspectj-maven.version}</version>
      <configuration>
        <aspectLibraries>
          <aspectLibrary>
            <groupId>edu.uchicago.cs.systems</groupId>
            <artifactId>wasabi</artifactId>
          </aspectLibrary>
        </aspectLibraries>
        <showWeaveInfo>true</showWeaveInfo>
        <verbose>true</verbose>
      </configuration>
      <executions>
        <execution>
          <goals>
            <goal>compile</goal>
            <goal>test-compile</goal>
          </goals>
        </execution>
      </executions>
    </plugin>
  </plugins>
</build>
```

Next, build the target application with WASABI woven in:
```bash
cd /path/to/target_application
mvn clean compile -T 8 -fn -DskipTests && mvn install -fn -DskipTests -B 2>&1 | tee wasabi-build.log
```

Successful weaving should produce log messages like this one:
```bash
[INFO] Join point 'method-execution(...)' in Type 'org.apache.hadoop.metrics2.util.SampleStat' ...
```

Users should also check out [examples](https://github.com/bastoica/wasabi/tree/wasabi-workspace/wasabi-testing) of target applications instrumented with WASABI from our `sosp24-ae` branch. These not only include detailed weaving steps, but also the modified `pom.xml` files.

### 4.2 Load-time weaving (Gradle, Ant, others)

Some applications use build systems other than Maven, like Gradle or Ant. In these cases, WASABI can be woven at load-time.

#### Load-time weaving with Gradle

First, add the AspectJ plugin and dependencies to your build.gradle file:
```xml
plugins {
  id 'io.freefair.aspectj.post-compile-weaving' version '8.1.0'
  id 'java'
}

dependencies {
  implementation 'org.aspectj:aspectjrt:1.9.19'
  aspect 'edu.uchicago.cs.systems:wasabi:1.0.0'
}
```

Next, configure AspectJ for load-time weaving:
```xml
compileJava {
  options.compilerArgs += ['-Xlint:none']
  doLast {
    javaexec {
      main = '-jar'
      args = [configurations.aspectj.getSingleFile(), '-inpath', sourceSets.main.output.classesDirs.asPath, '-aspectpath', configurations.aspect.asPath]
    }
  }
}
```

Finally, compile and build the project:
```bash
gradle clean build -i 2>&1 | tee wasabi-build.log
```

#### Load-time weaving with Ant

First, make sure AspectJ libraries (`aspectjrt.jar`, `aspectjtools.jar`) are available in your project.

Next, modify `build.xml` by adding the AspectJ tasks and specify WASABI in the aspect path:

```xml
<taskdef resource="org/aspectj/tools/ant/taskdefs/aspectjTaskdefs.properties"
         classpathref="aspectj-libs"/>

<target name="compile">
  <mkdir dir="build/classes"/>
  <ajc destdir="build/classes" source="1.8" target="1.8" fork="true" aspectpathref="wasabi-libs">
    <classpath>
      <pathelement path="src/main/java"/>
      <pathelement refid="aspectj-libs"/>
    </classpath>
    <sourcepath>
      <pathelement path="src/main/java"/>
    </sourcepath>
    <inpath>
      <pathelement path="src/main/java"/>
    </inpath>
  </ajc>
</target>
```

Finally, compile and build the project:
```bash
ant compile 2>&1 | tee wasabi-build.log
```

## 5. Configure fault injection policies and metadata

To specify fault injection policies and the precise injection locations, users need to create two types of files&mdash;a location data file (`.data`) and a policy configuration file (`.conf`).

A `.data` file describes the retry locations and their respective exceptions to be injected by Wasabi. It has the following format:
```xml
Retry location!!!Enclosing method!!!Retried method!!!Injection site!!!Exception
https://github.com/apache/hadoop/tree//ee7d178//hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/Client.java#L790!!!org.apache.hadoop.ipc.Client$Connection.setupIOstreams!!!org.apache.hadoop.ipc.Client$Connection.writeConnectionContext!!!Client.java:831!!!java.net.SocketException
https://github.com/apache/hadoop/tree//ee7d178//hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/namenode/ha/EditLogTailer.java#L609!!!org.apache.hadoop.hdfs.server.namenode.ha.EditLogTailer$MultipleNameNodeProxy.getActiveNodeProxy!!!org.apache.hadoop.ipc.RPC.getProtocolVersion!!!N/A!!!java.io.IOException
https://github.com/apache/hadoop/tree//ee7d178//hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/RPC.java#L419!!!org.apache.hadoop.ipc.RPC.waitForProtocolProxy!!!org.apache.hadoop.ipc.RPC.getProtocolProxy!!!RPC.java:421!!!java.net.ConnectException
...
```
where
* `Retry location` indicates the program locations of a retry (e.g. https://github.com/apache/hadoop/tree//ee7d178//hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/Client.java#L790)
* `Enclosing method` indicates the method from where the retry location is called (e.g. `org.apache.hadoop.ipc.Client$Connection.setupIOstreams`)
* `Retried method` indicates the method inside the retry logic ought to be retried (e.g. `org.apache.hadoop.ipc.Client$IpcStreams.setSaslClient`)
* `Injection site` indicates the source location (source file and line of code) where a retried method is called. Also, this represents the program location where Wasabi injects exceptions.
* `Exception` indicates the exception that Wasabi should throw at that location (e.g. `java.io.SocketException`)


A `.conf` file instructs WASABI to use a specific injection policy and load injection locations from a particular `.data` file and has the following structure:

```xml
retry_data_file: /absolute/path/to/data/file/example_retry_locations.data
injection_policy: max-count
max_injection_count: 10
```
where
* retry_data_file: Absolute path to a .data file specifying injection sites.
* injection_policy: One of no-injection, forever, or max-count.
* max_injection_count: Positive integer specifying the upper limit of injections (used with max-count policy).

The users can check out examples of `.data` and `.conf` files in the `./config` directory, or on the `sosp24-ae` [branch](https://github.com/bastoica/wasabi/tree/wasabi-workspace/wasabi-testing/config).


## Find retry bugs 

Once WASABI is successfuly build, woven into a target application, and configured, users can instruct WASABI to finding potential retry bugs.

To do so, users have two options:

1. Option #1 (recommended): run individual tests and instruct WASABI to inject faults at only one location during the test run. The reason is that, by desing, WASABI tries to force the test to either crash or hang. If this happens at the first injection location, subsequent injection locations will not get a chance to execute due to the test terminating (or hanging) early.
```bash
cd [target_application_path]
mvn clean install -U -fn -B -DskipTests 2>&1 | tee wasabi-build.log
mvn surefire:test -fn -B -DconfigFile="$(echo $HOME)/wasabi/wasabi-testing/config/example_hdfs.conf" -Dtest=[TEST_NAME] 2>&1 | tee wasabi-test.log
```

2. Option #2: run the entire test suite and inject faults at multiple locations in the same testing runs. Users can opt to inject faults at multiple locations in the same testing run if they are confident that injecting at an earlier location does not affect the execution of a later location. In this case, users can create a multi-location `.data` file (e.g., like [this one](https://github.com/bastoica/wasabi/blob/wasabi-workspace/wasabi-testing/config/hadoop/hadoop_retry_locations.data) for Hadoop).

```bash
cd [target_application_path]
mvn clean install -U -fn -B -DskipTests 2>&1 | tee wasabi-build.log
mvn test  -fn -B  -DconfigFile="$(echo $HOME)/wasabi/wasabi-testing/config/example_hdfs.conf" 2>&1 | tee wasabi-test.log
```

## 6. Running example: reproducing HDFS-17590 

To illustrate how WASABI work, we walk users through an example that reproduces [HDFS-17590](https://issues.apache.org/jira/browse/HDFS-17590)&mdash;a previously unknown retry bug uncovered by WASABI.

> [!NOTE]
> Users might observe a "build failure" message when building and testing Hadoop. This is expected as a few testing-related components of Hadoop need more configuration to build properly with the ACJ compiler. WASABI does not need those components to find retry bugs. See the "[Known issues](README.md#7-known-issues)" section below for more details.


1. Ensure the prerequisites are successfully installed (see "Getting Started" above)
   
2. Build and install WASABI (see "Building and installing WASABI" above)

3. Clone Hadoop (note: HDFS is part of Hadoop),
```bash
cd ~/wasabi-workspace/benchmarks
git clone https://github.com/apache/hadoop
```
and check out version/commit `60867de`:
```bash
cd ~/wasabi-workspace/benchmarks/hadoop
git checkout 60867de
```
Users can check whether `60867de` was successfully checked out by running
```bash
git log
```
and checking the output
```
commit 60867de422949be416948bd106419c771c7d13fd (HEAD)
Author: zhangshuyan <81411509+zhangshuyan0@users.noreply.github.com>
Date:   Mon Aug 21 10:05:34 2023 +0800

    HDFS-17151. EC: Fix wrong metadata in BlockInfoStriped after recovery. (#5938). Contributed by Shuyan Zhang.
    
    Signed-off-by: He Xiaoqiao <hexiaoqiao@apache.org>

```

4. Build and install Hadoop using the following commands. This is necessary to download and install any missing dependencies that might break Hadoop's test suite during fault injection.
```bash
mvn install -U -fn -B -DskipTests 2>&1 | tee wasabi-pass-install.log
```

5. Run the test that WASABI uses to trigger HDFS-17590 to confirm that the bug does not get triggered without fault injection
```bash
mvn surefire:test -fn -B -Dtest=TestFSEditLogLoader 2>&1 | tee wasabi-pass-test.log
```
by checking that the test runs successfully. First, checking that there is no `NullPointerException`
```bash
grep -A10 -B2 "NullPointerException" wasabi-pass-test.log
```
which should yield no output, as well as that all such tests passed
```bash
grep "Tests run.*TestFSEditLogLoader" wasabi-pass-test.log
```
which should yield a line similar to this (note that number of tests might differ slightly)
```bash
[INFO] Tests run: 26, Failures: 0, Errors: 0, Skipped: 0, Time elapsed: 154.223 s - in org.apache.hadoop.hdfs.server.namenode.TestFSEditLogLoader 
```

6. Copy a modified `pom.xml` file that allows WASABI to instrument (weave) Hadoop by running
```bash
cp pom.xml pom-original.xml
cp ~/wasabi-workspace/wasabi/wasabi-testing/config/hadoop/pom-hadoop.xml pom.xml
```
Note that these commands are making a copy of the original `pom.xml` and replace it with a slightly edited version that instructs the AJC compiler to instrument (weave) WASABI. Also, these alterations are specific to version `60867de`. Checking out another Hadoop commit ID requires adjustments. We provide instructions on how to adapt an original `pom.xml`, [here](README.md#instrumentation-weaving-instructions).

7. Instrument Hadoop with WASABI by running
```bash
mvn clean install -U -fn -B -DskipTests 2>&1 | tee wasabi-fail-install.log
```

8. Run the bug-triggering tests with fault injection
```bash
mvn surefire:test -fn -B -DconfigFile="$(echo $HOME)/wasabi-workspace/wasabi/wasabi-testing/config/hadoop/example.conf" -Dtest=TestFSEditLogLoader 2>&1 | tee wasabi-fail-test.log
```
and check the log to for `NullPointerException` errors
```bash
grep -A10 -B2 "NullPointerException" wasabi-fail-test.log
```
which should yield
```bash
[ERROR] Tests run: 26, Failures: 0, Errors: 2, Skipped: 0, Time elapsed: 137.645 s <<< FAILURE! - in org.apache.hadoop.hdfs.server.namenode.TestFSEditLogLoader
[ERROR] testErasureCodingPolicyOperations[0](org.apache.hadoop.hdfs.server.namenode.TestFSEditLogLoader)  Time elapsed: 22.691 s  <<< ERROR!
java.lang.NullPointerException
        at java.base/java.util.concurrent.ConcurrentHashMap.putVal(ConcurrentHashMap.java:1011)
        at java.base/java.util.concurrent.ConcurrentHashMap.put(ConcurrentHashMap.java:1006)
        at org.apache.hadoop.hdfs.DFSInputStream.addToLocalDeadNodes(DFSInputStream.java:184)
        at org.apache.hadoop.hdfs.DFSStripedInputStream.createBlockReader(DFSStripedInputStream.java:279)
        at org.apache.hadoop.hdfs.StripeReader.readChunk(StripeReader.java:304)
        at org.apache.hadoop.hdfs.StripeReader.readStripe(StripeReader.java:335)
        at org.apache.hadoop.hdfs.DFSStripedInputStream.readOneStripe(DFSStripedInputStream.java:320)
        at org.apache.hadoop.hdfs.DFSStripedInputStream.readWithStrategy(DFSStripedInputStream.java:415)
        at org.apache.hadoop.hdfs.DFSInputStream.read(DFSInputStream.java:919)
        at java.base/java.io.DataInputStream.read(DataInputStream.java:102)
```    

## 7. Known issues

### 7.1 AspectJ Maven plugin circular dependency and versioning issues

WASABI imports plugins that might also be imported by the target application. Users need to manually resolve potential circular dependencies or plugin version incompatibilities. Users could also reference [this](https://github.com/dev-aspectj/aspectj-maven-plugin/issues/143) issue in the `aspectj-maven-plugin` repository for suggestions on how to tackle such issues.

### 7.2 Build failures after weaving

The AspectJ compiler and supporting plugins might not be able to weave (instrument) all modules of a target successfully. While users are encouraged to address this, we recommend disregarding modules that are not critical to the core functionality of the application (e.g., benchmarking modules) or that do not implement or test retry-related code.

For example, when reproducing HDFS-17590, users might observe a "build failure" message at the end of the build and testing processes. This is expected, as a few benchmark-related components of Hadoop require extra configuration for the AJC to compile them successfully. However, WASABI does not need these components to build correctly in order to find retry bugs. For reference, this is the original build log that WASABI encountered when building Hadoop. Note that the core components of Hadoop (common and client), HDFS, Yarn, and MapReduce all built successfully.

<details>
<summary>Hadoop `60867de` build log (expand for details):</summary>

```bash
[INFO] ------------------------------------------------------------------------
[INFO] Reactor Summary for Apache Hadoop Main 3.4.0-SNAPSHOT:
[INFO] 
[INFO] Apache Hadoop Main ................................. SUCCESS [  4.399 s]
[INFO] Apache Hadoop Build Tools .......................... SUCCESS [  2.222 s]
[INFO] Apache Hadoop Project POM .......................... SUCCESS [  1.716 s]
[INFO] Apache Hadoop Annotations .......................... SUCCESS [  3.483 s]
[INFO] Apache Hadoop Project Dist POM ..................... SUCCESS [  0.098 s]
[INFO] Apache Hadoop Assemblies ........................... SUCCESS [  0.094 s]
[INFO] Apache Hadoop Maven Plugins ........................ SUCCESS [  8.806 s]
[INFO] Apache Hadoop MiniKDC .............................. SUCCESS [ 16.738 s]
[INFO] Apache Hadoop Auth ................................. SUCCESS [01:15 min]
[INFO] Apache Hadoop Auth Examples ........................ SUCCESS [  1.117 s]
[INFO] Apache Hadoop Common ............................... SUCCESS [01:34 min]
[INFO] Apache Hadoop NFS .................................. SUCCESS [ 15.503 s]
[INFO] Apache Hadoop KMS .................................. SUCCESS [  3.521 s]
[INFO] Apache Hadoop Registry ............................. SUCCESS [  3.468 s]
[INFO] Apache Hadoop Common Project ....................... SUCCESS [  0.060 s]
[INFO] Apache Hadoop HDFS Client .......................... SUCCESS [ 52.968 s]
[INFO] Apache Hadoop HDFS ................................. SUCCESS [ 57.425 s]
[INFO] Apache Hadoop HDFS Native Client ................... SUCCESS [  0.451 s]
[INFO] Apache Hadoop HttpFS ............................... SUCCESS [  4.092 s]
[INFO] Apache Hadoop HDFS-NFS ............................. SUCCESS [  1.579 s]
[INFO] Apache Hadoop YARN ................................. SUCCESS [  0.052 s]
[INFO] Apache Hadoop YARN API ............................. SUCCESS [ 15.454 s]
[INFO] Apache Hadoop YARN Common .......................... SUCCESS [ 27.587 s]
[INFO] Apache Hadoop YARN Server .......................... SUCCESS [  0.045 s]
[INFO] Apache Hadoop YARN Server Common ................... SUCCESS [ 16.038 s]
[INFO] Apache Hadoop YARN ApplicationHistoryService ....... SUCCESS [  5.012 s]
[INFO] Apache Hadoop YARN Timeline Service ................ SUCCESS [  3.239 s]
[INFO] Apache Hadoop YARN Web Proxy ....................... SUCCESS [  2.122 s]
[INFO] Apache Hadoop YARN ResourceManager ................. SUCCESS [ 29.966 s]
[INFO] Apache Hadoop YARN NodeManager ..................... SUCCESS [ 25.820 s]
[INFO] Apache Hadoop YARN Server Tests .................... SUCCESS [  1.488 s]
[INFO] Apache Hadoop YARN Client .......................... SUCCESS [  4.974 s]
[INFO] Apache Hadoop MapReduce Client ..................... SUCCESS [  0.593 s]
[INFO] Apache Hadoop MapReduce Core ....................... SUCCESS [ 11.157 s]
[INFO] Apache Hadoop MapReduce Common ..................... SUCCESS [  3.654 s]
[INFO] Apache Hadoop MapReduce Shuffle .................... SUCCESS [  3.475 s]
[INFO] Apache Hadoop MapReduce App ........................ SUCCESS [  5.335 s]
[INFO] Apache Hadoop MapReduce HistoryServer .............. SUCCESS [  3.995 s]
[INFO] Apache Hadoop MapReduce JobClient .................. SUCCESS [  6.776 s]
[INFO] Apache Hadoop Distributed Copy ..................... SUCCESS [  2.958 s]
[INFO] Apache Hadoop Mini-Cluster ......................... SUCCESS [  0.903 s]
[INFO] Apache Hadoop Federation Balance ................... SUCCESS [  1.683 s]
[INFO] Apache Hadoop HDFS-RBF ............................. SUCCESS [ 10.150 s]
[INFO] Apache Hadoop HDFS Project ......................... SUCCESS [  0.042 s]
[INFO] Apache Hadoop YARN SharedCacheManager .............. SUCCESS [  1.171 s]
[INFO] Apache Hadoop YARN Timeline Plugin Storage ......... SUCCESS [  1.375 s]
[INFO] Apache Hadoop YARN TimelineService HBase Backend ... SUCCESS [  0.044 s]
[INFO] Apache Hadoop YARN TimelineService HBase Common .... SUCCESS [  9.957 s]
[INFO] Apache Hadoop YARN TimelineService HBase Client .... SUCCESS [ 21.167 s]
[INFO] Apache Hadoop YARN TimelineService HBase Servers ... SUCCESS [  0.044 s]
[INFO] Apache Hadoop YARN TimelineService HBase Server 1.7  SUCCESS [  2.516 s]
[INFO] Apache Hadoop YARN TimelineService HBase tests ..... SUCCESS [ 20.933 s]
[INFO] Apache Hadoop YARN Router .......................... SUCCESS [  4.274 s]
[INFO] Apache Hadoop YARN TimelineService DocumentStore ... SUCCESS [ 16.551 s]
[INFO] Apache Hadoop YARN GlobalPolicyGenerator ........... SUCCESS [  2.509 s]
[INFO] Apache Hadoop YARN Applications .................... SUCCESS [  0.042 s]
[INFO] Apache Hadoop YARN DistributedShell ................ SUCCESS [  1.558 s]
[INFO] Apache Hadoop YARN Unmanaged Am Launcher ........... SUCCESS [  0.833 s]
[INFO] Apache Hadoop YARN Services ........................ SUCCESS [  0.038 s]
[INFO] Apache Hadoop YARN Services Core ................... SUCCESS [  5.323 s]
[INFO] Apache Hadoop YARN Services API .................... SUCCESS [  1.736 s]
[INFO] Apache Hadoop YARN Application Catalog ............. SUCCESS [  0.040 s]
[INFO] Apache Hadoop YARN Application Catalog Webapp ...... SUCCESS [01:30 min]
[INFO] Apache Hadoop YARN Application Catalog Docker Image  SUCCESS [  0.073 s]
[INFO] Apache Hadoop YARN Application MaWo ................ SUCCESS [  0.054 s]
[INFO] Apache Hadoop YARN Application MaWo Core ........... SUCCESS [  1.153 s]
[INFO] Apache Hadoop YARN Site ............................ SUCCESS [  0.054 s]
[INFO] Apache Hadoop YARN Registry ........................ SUCCESS [  0.563 s]
[INFO] Apache Hadoop YARN UI .............................. SUCCESS [  0.357 s]
[INFO] Apache Hadoop YARN CSI ............................. SUCCESS [ 21.231 s]
[INFO] Apache Hadoop YARN Project ......................... SUCCESS [  0.695 s]
[INFO] Apache Hadoop MapReduce HistoryServer Plugins ...... SUCCESS [  0.859 s]
[INFO] Apache Hadoop MapReduce NativeTask ................. SUCCESS [  2.120 s]
[INFO] Apache Hadoop MapReduce Uploader ................... SUCCESS [  1.467 s]
[INFO] Apache Hadoop MapReduce Examples ................... SUCCESS [  2.022 s]
[INFO] Apache Hadoop MapReduce ............................ SUCCESS [  0.783 s]
[INFO] Apache Hadoop MapReduce Streaming .................. SUCCESS [  3.502 s]
[INFO] Apache Hadoop Client Aggregator .................... SUCCESS [  0.872 s]
[INFO] Apache Hadoop Dynamometer Workload Simulator ....... SUCCESS [  1.504 s]
[INFO] Apache Hadoop Dynamometer Cluster Simulator ........ SUCCESS [  1.659 s]
[INFO] Apache Hadoop Dynamometer Block Listing Generator .. SUCCESS [  1.456 s]
[INFO] Apache Hadoop Dynamometer Dist ..................... SUCCESS [  1.242 s]
[INFO] Apache Hadoop Dynamometer .......................... SUCCESS [  0.040 s]
[INFO] Apache Hadoop Archives ............................. SUCCESS [  0.948 s]
[INFO] Apache Hadoop Archive Logs ......................... SUCCESS [  0.978 s]
[INFO] Apache Hadoop Rumen ................................ SUCCESS [  2.024 s]
[INFO] Apache Hadoop Gridmix .............................. SUCCESS [  1.962 s]
[INFO] Apache Hadoop Data Join ............................ SUCCESS [  0.963 s]
[INFO] Apache Hadoop Extras ............................... SUCCESS [  1.132 s]
[INFO] Apache Hadoop Pipes ................................ SUCCESS [  0.039 s]
[INFO] Apache Hadoop Amazon Web Services support .......... SUCCESS [ 16.110 s]
[INFO] Apache Hadoop Kafka Library support ................ SUCCESS [  2.281 s]
[INFO] Apache Hadoop Azure support ........................ SUCCESS [  8.403 s]
[INFO] Apache Hadoop Aliyun OSS support ................... SUCCESS [  6.307 s]
[INFO] Apache Hadoop Scheduler Load Simulator ............. SUCCESS [  2.002 s]
[INFO] Apache Hadoop Resource Estimator Service ........... SUCCESS [  2.300 s]
[INFO] Apache Hadoop Azure Data Lake support .............. SUCCESS [  2.248 s]
[INFO] Apache Hadoop Image Generation Tool ................ SUCCESS [  1.332 s]
[INFO] Apache Hadoop Tools Dist ........................... SUCCESS [  0.596 s]
[INFO] Apache Hadoop OpenStack support .................... SUCCESS [  0.049 s]
[INFO] Apache Hadoop Common Benchmark ..................... FAILURE [  2.949 s]
[INFO] Apache Hadoop Tools ................................ SUCCESS [  0.039 s]
[INFO] Apache Hadoop Client API ........................... SUCCESS [04:31 min]
[INFO] Apache Hadoop Client Runtime ....................... SUCCESS [04:55 min]
[INFO] Apache Hadoop Client Packaging Invariants .......... FAILURE [  0.197 s]
[INFO] Apache Hadoop Client Test Minicluster .............. SUCCESS [08:43 min]
[INFO] Apache Hadoop Client Packaging Invariants for Test . FAILURE [  0.115 s]
[INFO] Apache Hadoop Client Packaging Integration Tests ... SUCCESS [  1.206 s]
[INFO] Apache Hadoop Distribution ......................... SUCCESS [  0.304 s]
[INFO] Apache Hadoop Client Modules ....................... SUCCESS [  0.042 s]
[INFO] Apache Hadoop Tencent COS Support .................. SUCCESS [  1.993 s]
[INFO] Apache Hadoop OBS support .......................... FAILURE [  6.322 s]
[INFO] Apache Hadoop Cloud Storage ........................ SUCCESS [  1.423 s]
[INFO] Apache Hadoop Cloud Storage Project ................ SUCCESS [  0.039 s]
[INFO] ------------------------------------------------------------------------
[INFO] BUILD FAILURE
[INFO] ------------------------------------------------------------------------
[INFO] Total time:  31:50 min
[INFO] Finished at: 2024-08-14T06:26:40Z
[INFO] ------------------------------------------------------------------------
```
</details>

### 7.3 Bare metal versus containerized deployments

WWASABI was tested on a bare metal machine. Fundamentally, there are no limitations to running WASABI in a containerized environment. However, there are known issues related to the Hadoop and HBase benchmarks used to evaluate WASABI in our [paper](https://bastoica.github.io/files/papers/2024_sosp_wasabi.pdf).

In short, some Hadoop and HBase tests require access to a non-virtualized, physical network. Without this, users might encounter errors such as
```
ERROR regionserver.HRegionServer: Master passed us a different hostname to use; was=grimlock, but now=169.254.3.1
```
These errors occur due to a hostname-to-IP mismatch in the network setup of your system, not because of an issue with WASABI. The likely cause is a misconfigured `/etc/hosts` file, multiple network interfaces on your machine, or running our tool in a containerized environment (e.g., docker).
