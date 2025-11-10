# YourBenchmarkName

## Scenario Description

Provide a summary of your scenarios here. This section should give an overview of the context, objectives, and key elements involved in your scenarios.

### Task Details

Describe your task in detail, including:

- **Input**: Specify the type of input data required for the task.
- **Output**: Define the expected output from the task.
- **Evaluation**: Explain how to evaluate the output, including any metrics or criteria used to measure performance.

## Benchmark Setup

### Test in Docker

To test your benchmark in a Docker container, follow these steps:

1. Build the Docker image using the provided Dockerfile. You can do this by running the following command in the terminal:

   ```sh
   docker build -t your_benchmark_image .
   ```

2. Once the image is built, you can run it using the following command:

   ```sh
   docker run -it --rm your_benchmark_image
   # docker run --rm your_benchmark_image
   ```

3. Inside the container, navigate to the appropriate directory and execute the benchmark script to start the testing process.

   ```sh
   ./run.sh
   ```

### Maunaly Test

To manually test your benchmark, follow these steps:

#### Install Dependencies

To install and configure your benchmark, follow these steps:

1. Run the `install.sh` script to set up the environment and install necessary dependencies. You can simply execute the following command:

   ```sh
   ./install.sh
   ```

#### Run

To run your benchmark and obtain results for a specific task and model, follow these steps:

1. Review the `run.sh` script to understand the expected commands and parameters.
2. Execute the `run.sh` script to start the benchmark. The script will guide you through the process and generate the results.

Feel free to adjust the details to better fit your specific scenario and requirements. Let me know if there's anything else you need!
