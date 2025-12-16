# Artifact Evaluation Instructions for "Anvil: Verifying Liveness of Cluster Management Controllers"

This document is for OSDI'2024 artifact evaluation.

## Artifact goal
In the paper, we make the claim that
>  We use Anvil to verify three Kubernetes controllers for managing ZooKeeper, RabbitMQ, and FluentBit, which can readily be deployed in Kubernetes platforms and are comparable in terms of features and performance to widely used unverified controllers.

The goal is to reproduce the key results to support the claim. Specifically, the key results are (1) verification results in Figure 1 in Section 7 and (2) performance results in Figure 3 in Section 7.

The entire artifact evaluation process can take about 9 hours (mostly machine time).

1. [Kick-the-tires Instructions](#kick-the-tires-instructions-15-compute-hours--6-human-minutes)
2. [Full Evaluation Instructions](#full-evaluation-instructions-7-compute-hours--6-human-minutes)

## Kick-the-tires Instructions (~1.5 compute-hours + ~6 human-minutes)

Following kick-the-tires instructions, you will (1) verify one controller using the container image we prepared, and (2) run a small subset of the workloads used for evaluating the controller's performance.

### Running workloads of one controller (~1.5 compute-hours + ~5 human-minutes)

The instructions in this section require some environment setup to run the controller workloads. To set up the environment you need to follow these broad steps.

**Step 1: setting up the environment**

* A Linux system with Docker support. If Docker not installed, run
  ```bash
  sudo apt-get update && sudo apt-get upgrade -y
  sudo apt-get install docker.io
  sudo systemctl enable --now docker
  sudo groupadd docker 2>/dev/null || true
  sudo usermod -aG docker "$USER"
  newgrp docker
  ```
* Python 3.10 or newer.
* Install `pip3` by running `sudo apt install python3-pip`
* Clone the repo recursively by running `git clone --recursive --branch anvil-dev https://github.com/xlab-uiuc/acto.git`
* Install Python dependencies by running in the project directory 
  ```bash
  python3 -m venv .venv
  source .venv/bin/activate
  sudo apt install python3-pip
  pip3 install -r acto/requirements.txt
  pip3 install -r acto/requirements-dev.txt
  ```
* Install Golang:
  ```bash
  sudo apt-get install -y golang
  export PATH=$HOME/go:$HOME/go/bin:$PATH
  ```
* Install `Kind` by running `go install sigs.k8s.io/kind@v0.20.0`
* Install `Kubectl` by running `curl -LO https://dl.k8s.io/release/v1.22.9/bin/linux/amd64/kubectl` and `sudo install -o root -g root -m 0755 kubectl /usr/local/bin/kubectl`

Run all the instructions below inside the cloned `acto` repo.

**Step 2: run the workload**

We suggest you use `tmux` when running on remote machines as the command can take hours.
```bash
cd $HOME/osdi24_anvil/acto/
bash anvil-ae-one-controller.sh 0.01
```
It takes ~1.5 hours to finish on CloudLab c6420. Note that if you chose to manually set up the environment, you need to replace `$HOME/osdi24_anvil/acto/` with the path to the cloned `acto` repo on your machine instead.

**Step 3: check the performance result**
```bash
cat anvil-table-3.txt
```
You should see a table like this:
```
| Controller   |   Verified (Anvil) Mean |   Verified (Anvil) Max |   Reference (unverified) Mean |   Reference (unverified) Max |
|--------------|-------------------------|------------------------|-------------------------------|------------------------------|
| Zookeeper    |                 149.953 |                159.953 |                       141.854 |                      160.174 |
```
Note that the absolute numbers depends on the platform. If you do not see the expected table, please let us know.

## Full Evaluation Instructions (~7 compute-hours + ~6 human-minutes)

Following full evaluation instructions, you will reproduce the verification results in Table 1 and the performance results in Table 3. These are the key results that support the claim in the paper. The absolute number of the time-related results heavily depend on the platform, but we will **highlight** the key pattern you should be able to observe.

### Reproducing Performance Results in Table 3 (~7 compute-hours + ~3 human-minutes)

Following the instructions, you will reproduce the key results that the verified controllers achieve comparable performance to the unverified reference controllers as shown in Table 3.

You will reuse the CloudLab machine as in the [Kick-the-tires Instructions](#running-workloads-of-one-controller-15-compute-hours--5-human-minutes).

We suggest you use `tmux` when running on remote machines as the command will take hours.

In the path `$HOME/osdi24_anvil/acto/` inside your CloudLab machine, run
```bash
bash anvil-ae-sampled.sh 0.01
```
This command runs 5% of the workloads for the three controllers and their unverified references. It takes ~7 hours to finish on CloudLab c6420. After it's done, to see the generated Table 3, run
```bash
cat anvil-table-3.txt
```
and you should see a generated table like this:
```
| Controller   |   Verified (Anvil) Mean |   Verified (Anvil) Max |   Reference (unverified) Mean |   Reference (unverified) Max |
|--------------|-------------------------|------------------------|-------------------------------|------------------------------|
| Zookeeper    |                 149.953 |                159.953 |                       141.854 |                      160.174 |
| RabbitMQ     |                 201.167 |                356.158 |                       202.159 |                      356.013 |
| FluentBit    |                  32.087 |                 33.049 |                        29.634 |                       33.26  |
```
The numbers are the execution time (in milliseconds) it takes for the verified/reference controller to do reconciliation. The absolute numbers depend on the platform. You might observe that the execution times are shorter compared to the numbers reported in the paper. This is because the machine configuration and Acto (the tool we use to run workloads) have changed since the submission. **Regardless of the platform, you should still be able to observe that the verified controllers are NOT significantly slower than their unverified references.** The execution time of each verified controller should be within 2.5X of the execution time of the corresponding reference controller, in terms of both mean and max time. In fact, in most cases their differences are negligible (as shown above).

