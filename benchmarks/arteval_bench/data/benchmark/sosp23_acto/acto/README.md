# Artifact Evaluation for "Automatic Testing for Correct Operations of Cloud Systems" ([SOSP'23 AE #77](https://sosp23ae.hotcrp.com/paper/77))

# 1. Artifact Goals

The instructions will reproduce the key results in Tables 5, 6, 7, and 8 in Section 6 of the submission. That is, the following instructions will lead you to (1) reproduce all 56 bugs found by Acto and oracles needed to find them, and (2) reproduce the test generation.

The entire artifact process can take around 2 hours if run with a concurrency of 16 workers (e.g., using the CloudLab machine we suggest); it will take about 17 hours if running sequentially (with no concurrent worker).

If you have any questions, please contact us via email or HotCRP.

> [!NOTE]
> This artifact version has removed the Reddis and Knative operators since the originally faulty images are no longer available. The current version also applies patch [#8ecdcda](https://github.com/xlab-uiuc/acto/commit/8ecdcda5a51d7c5625e49802bbd1bc75c0cf07ef) that allows Acto to load operators from pre-packaged archives when the original images are no longer availble for download.

# 2. Prerequisites

## Setting up local environment
 
* A Linux system with Docker support and configure Docker
  ```bash
  sudo apt-get update && sudo apt-get upgrade -y
  sudo apt-get install docker.io
  sudo systemctl enable --now docker
  sudo groupadd docker 2>/dev/null || true
  sudo usermod -aG docker "$USER"
  newgrp docker
  ```
* Python 3.8 or newer
  ```bash
  sudo apt update
  sudo apt install software-properties-common -y
  sudo add-apt-repository ppa:deadsnakes/ppa -y
  sudo apt update
  sudo apt install python3.8 python3.8-venv -y
  ```
* Install Python dependencies by running in the project directory 
  ```bash
  python3.8 -m venv .venv
  source .venv/bin/activate
  sudo apt install python3-pip
  pip3 install -r acto/requirements.txt
  ```
* Install Golang:
  ```bash
  sudo apt-get install -y golang
  export PATH=$HOME/go:$HOME/go/bin:$PATH
  ```
* Install `Kind` by running `go install sigs.k8s.io/kind@v0.20.0`
* Install `Kubectl` by running `curl -LO https://dl.k8s.io/release/v1.22.9/bin/linux/amd64/kubectl` and `sudo install -o root -g root -m 0755 kubectl /usr/local/bin/kubectl`
* Configure inotify limits (need to rerun after reboot)
  * `sudo sysctl fs.inotify.max_user_instances=1024`
  * `sudo sysctl fs.inotify.max_user_watches=1048576`

# 3. Kick-the-tire Instructions (10 minutes)

We prepared a simple example -- reproducing a bug found by Acto -- to help check obvious setup problems. 

First, build the dependant modules:

```sh
cd $HOME/sosp23_acto/acto/
make
```

Then, reproduce the OCK-RedisOp-287 bug by running:

```sh
python3 reproduce_bugs.py --bug-id rbop-928
```

Expected results:

```text
Reproducing bug rbop-928 in RabbitMQOp!
Preparing required images...
Deleting cluster "acto-0-cluster-0" ...
Creating a Kind cluster...
Deploying operator...
Operator deployed
Deleting cluster "acto-0-cluster-0" ...
Deleted nodes: ["acto-0-cluster-0-worker3" "acto-0-cluster-0-control-plane" "acto-0-cluster-0-worker" "acto-0-cluster-0-worker2"]
Creating a Kind cluster...
Deploying operator...
Operator deployed
Bug rbop-928 reproduced!
Bug category: undesired_state
```

# 4. Full Evaluation Instructions (2+ hours)

## Reproducing Tables 5, 6, 7

To reproduce the 56 bugs in Table 5, please execute the tests by running:

```sh
cd ~/workdir/acto/
make
python3 reproduce_bugs.py -n <NUM_WORKERS>
```

Using the c6420 profile we recommend, run the tests with 16 workers `-n 16` and it will take about 80 minutes to finish.

Using the c8220 profile we cecommend, run the tests with 8 workers `-n 8` and it will take about 3 hours to finish.

We suggest starting this long-running experiment in a tmux or screen session.

**Caution**: running too many workers at the same time may overload your machine, and Kind would fail to bootstrap Kubernetes clusters. If you are not running the experiment using our recommended CloudLab profile, please default the number of workers to `1`. Running this step sequentially takes approximately 17 hours.

<details><summary>What does the reproduce script do?</summary>For each bug, the reproduction code runs Acto with tests needed to reproduce the bug. It checks if every bug is reproducible and outputs Table 5. The code uses each bug’s consequence labels to reproduce Table 6. The code also checks which oracles are used by Acto to detect the bug, and reproduces Table 7.</details>

After it finishes, you will find `table5.txt`, and `table6.txt`, and `table7.txt` in the current directory.

The `table5.txt` should look like below:

```text
Operator         Undesired State    System Error    Operator Error    Recovery Failure    Total
-------------  -----------------  --------------  ----------------  ------------------  -------
CassOp                         2               0                 0                   2        4
CockroachOp                    3               0                 2                   0        5
KnativeOp                      1               0                 2                   0        3
OCK-RedisOp                    4               1                 3                   1        9
OFC-MongoDBOp                  3               1                 2                   2        8
PCN-MongoDBOp                  4               0                 0                   1        5
RabbitMQOp                     3               0                 0                   0        3
SAH-RedisOp                    2               0                 0                   1        3
TiDBOp                         2               1                 0                   1        4
XtraDBOp                       4               0                 1                   1        6
ZookeeperOp                    4               1                 0                   1        6
Total                         32               4                10                  10       56
```

The `table6.txt` should look like below:

```text
Consequence          # Bugs
-----------------  --------
System failure            5
Reliability issue        15
Security issue            2
Resource issue            9
Operation outage         18
Misconfiguration         15
```

The `table7.txt` should look like below:

```text
Test Oracle                                          # Bugs (Percentage)
---------------------------------------------------  ---------------------
Consistency oracle                                   23 (41.07%)
Differential oracle for normal state transition      25 (44.64%)
Differential oracle for rollback state transition    10 (17.86%)
Regular error check (e.g., exceptions, error codes)  14 (25.00%)
```

## Reproducing Table 8 (1 minute)

For Table 8, we reproduce "#Ops" (Column 5) Acto generated during test campaigns in our evaluation. We provide test data we collected in our evaluation of Acto and reproduce Table 8 based on the evaluation data.

Note: Running test campaigns of all the 11 operators with a single worker would take around 1,920 machine hours, or 160 hours with the Cloudlab Clemson c6420 machine with the level of parallelism in our evaluation. We provide instructions in the next section if you’d like to run that.


To collect #Ops Acto generated for each test campaign, run the following script,

```sh
python3 collect_number_of_ops.py
```

The output should look like this:

```text
Operator         # Operations
-------------  --------------
CassOp                    568
CockroachOp               371
KnativeOp                 774
OCK-RedisOp               597
OFC-MongoDBOp             434
PCN-MongoDBOp            1749
RabbitMQOp                394
SAH-RedisOp               718
TiDBOp                    824
XtraDBOp                 1950
ZookeeperOp               740
```

## Running all the test campaigns of all the operators (Optional)
<details><summary>Click to show detailed instructions</summary>

Please note that running all the test campaigns on the CloudLab Clemson c6420 could take 160 machine hours. In our evaluation, we did all the entire runs progressively and ran different test campaigns on different machines at the same time, with a cluster of 10 CloudLab machines. We suggest you reserve 10 machines, instead of doing it with one machine.

You can refer to [test_campaign.md](test_campaign.md) for detailed commands for running each test campaign.

If you would like to try out an end-to-end test campaign, you can do it with the following commands (taking the RabbitMQ operator as an example).

Build the dependant modules as in previous sections if you haven't done so:

```sh
cd ~/workdir/acto/
make
```

Run the test campaign:

```sh
python3 -m acto --config data/rabbitmq-operator/config.json --num-workers 16 --workdir testrun-rabbitmq
```

</details>

## Interpreting the test results (Optional)

We provide the instructions for interpreting the results produced by Acto's test campaign.

Acto's test campaign creates a work directory (specific by the argument `--workdir`).
Inside the work directory, there are a list of `trial-*` directories (Acto creates a new `trial-*` directory when it raises an alarm).
Inside each `trial-*` directory, you can find the following files:
- `mutated-*.yaml`: These files are the inputs Acto submitted to Kubernetes to run the state transitions. Concretely, Acto first applies `mutated-0.yaml`, and wait for the system to converge, and then applies `mutated-1.yaml`, and so on.
- `system-state-*.json`: After each step submitting `mutated-*.yaml`, Acto collects the system state and store it as `system-state-*.json`. This file contains the serialized state objects from Kubernetes.
- `cli-output-*.log` and `operator-*.log`: The command line result and operator log after submitting the input.
- `delta-*.log`: This file contains two parts. This file is for convenient debug purposes:
  - Input delta: The delta between current input and last input
  - System delta: The delta between current system state and last system state
- `events.log`: The list of Kubernetes events happened throughout this trial, to help diagnosis.
- `result.json`: The result for this trial. It contains results for each oracle Acto runs. If an oracle fails, the corresponding field in the `result.json` would contain an error message. Otherwise, the corresponding field in the `result.json` would be `Pass` or `None`. Note that Acto could write `result.json` even if there is no error (e.g. when the test campaign is finished), in that case every oracle field in the `result.json` will be `Pass` or `None`. Legend for relevant fields in the `result.json`:
  - `duration`: amount of time taken for this trial
  - `error`:
    - `crash_result`: if any container crashed or not
    - `health_result`: if any statefulset or deployment is unhealthy, by comparing the ready replicas in status and desired replicas in spec
    - `state_result`: consistency oracle, checking if the desired system state matches the actual system state
    - `log_result`: if the log indicates invalid input
    - `custom_result`: result of custom oracles
    - `recovery_result`: if the recovery step is successful after the error state

