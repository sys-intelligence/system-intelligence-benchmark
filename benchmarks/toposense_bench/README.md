# TopoSense-Bench: Semantic-Spatial Sensor Scheduling

**TopoSense-Bench** is a large-scale, rigorous benchmark designed to evaluate Large Language Models (LLMs) on the **Semantic-Spatial Sensor Scheduling (S³)** problem.

Originating from the **ACM MobiCom '26** paper *"IoT-Brain: Grounding LLMs for Semantic-Spatial Sensor Scheduling"*, this benchmark tests an agent's ability to translate high-level natural language user intents (e.g., *"Find my backpack lost between the library and the gym"*) into precise physical sensor activation plans within a large-scale digital twin.

## 📊 Overview

- **Source**: Hosted on [Hugging Face](https://huggingface.co/datasets/IoT-Brain/TopoSense-Bench) (Seamlessly integrated via the `datasets` library).
- **Scale**:
  - **5,250** Natural Language Queries.
  - **2,510** Sensors (Cameras).
  - **161** Floor Plans across **33** Buildings.
- **Problem Domain**: Embodied AI, IoT, Spatial Reasoning, and RAG (Retrieval-Augmented Generation).

## 🎯 Task Taxonomy

The benchmark categorizes queries into three tiers of complexity based on the spatial scope and reasoning difficulty:

- **Tier 1: Intra-Zone Perception**
  - Simple queries focused on specific rooms or focal areas (e.g., *"Check the entrance of the conference hall"*).
- **Tier 2: Intra-Building Coordination**
  - Complex queries requiring navigation across multiple floors within a single building (e.g., *"Track the path from the 4th-floor lab to the ground floor exit"*).
- **Tier 3: Inter-Building Coordination**
  - Long-horizon queries involving transitions between outdoor spaces and multiple buildings (e.g., *"I walked from the Library to the Gym, check cameras along the way"*).

## ⚙️ Evaluation Methodology

Unlike standard QA benchmarks, TopoSense-Bench employs a **Retrieval-Augmented Generation (RAG)** workflow to simulate realistic sensor scheduling:

1.  **Context Retrieval**: The system dynamically retrieves the relevant topological map data (textual representation of buildings/floors) based on the user's query using a heuristic `TopologyManager`.
2.  **Reasoning**: The LLM acts as a scheduler. It must analyze the provided map data and the user's intent to identify the specific sensor node ID that best satisfies the request.
3.  **Scoring**: The evaluation uses a parsing-based exact match metric. It compares the core identifier in the LLM's output against the ground truth sensor ID (e.g., `teaching_building_1_camera_03`).

## 🚀 Quick Start

### 1. Installation

Ensure you are in the `benchmarks/toposense_bench` directory, then install the required dependencies:

```bash
pip install -r requirements.txt
```

### 2. Configuration

Create or edit `env.toml` to configure your LLM provider. This benchmark uses `litellm` for model calls.

```toml
[llm]
# Example for OpenAI
OPENAI_API_KEY = "sk-..."

# Example for DeepSeek (OpenAI-Compatible)
# OPENAI_API_KEY = "sk-..."
# OPENAI_API_BASE = "https://api.deepseek.com"
```

### 3. Run Evaluation

Run the evaluation script. You must specify the model name.

> **Note**: If using a non-OpenAI provider (like DeepSeek or Qwen) via the OpenAI-compatible endpoint, please add the `openai/` prefix to the model name.

```bash
# Run with GPT-4o
bash run.sh "gpt-4o"

# Run with DeepSeek-Chat
bash run.sh "openai/deepseek-chat"
```

### 4. Results

After the run completes, results will be saved in the `outputs/` directory:
- `summary.json`: Overall accuracy and breakdown by task tier.
- `results.jsonl`: Detailed logs including retrieval status, model input/output, and correctness for every query.

## 📚 Citation

If you use this benchmark in your research, please cite our MobiCom '26 paper:

```bibtex
@inproceedings{iotbrain2026,
  title={IoT-Brain: Grounding LLMs for Semantic-Spatial Sensor Scheduling},
  author={Anonymous Author(s)},
  booktitle={Proceedings of the 32nd Annual International Conference on Mobile Computing and Networking (MobiCom '26)},
  year={2026}
}
```
