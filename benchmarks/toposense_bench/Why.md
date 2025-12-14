# Why TopoSense-Bench?

## The Problem: The Semantic-Physical Mapping Gap
Modern IoT systems are transitioning from passive monitoring to intent-driven operation. However, a critical gap exists between high-level human intent (e.g., *"Find my backpack lost between the library and the gym"*) and the precise physical sensor actions required to fulfill it.

Existing benchmarks often focus on pure QA or code generation, overlooking the **embodied** and **spatial** reasoning capabilities required for real-world cyber-physical systems.

## The Solution: Semantic-Spatial Sensor Scheduling (S³)
TopoSense-Bench introduces the S³ challenge, requiring LLMs to:
1.  **Reason Spatially**: Understand complex topological relationships (connectivity, floor transitions) in a large-scale digital twin.
2.  **Act Proactively**: Select the optimal subset of sensors from a massive network (2,510 cameras) to satisfy a query, rather than just answering a text question.
3.  **Ground in Reality**: Map vague natural language to concrete sensor identifiers (e.g., `teaching_building_1_camera_03`).

## Impact
By mastering this benchmark, LLMs demonstrate the capability to serve as the "brain" for large-scale smart city and smart campus infrastructures, moving beyond chatbots to actionable physical agents.