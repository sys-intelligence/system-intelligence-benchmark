"""Helper to load and index topology data from Hugging Face."""

from datasets import load_dataset
from loguru import logger


class TopologyManager:
    """
    Manages the loading and indexing of the topological knowledge base.
    """

    def __init__(self):
        # Index structure: { "building_name": { "floor": "content..." } }
        self.topo_index = {}
        self._load_data()

    def _load_data(self):
        """Loads the topology dataset from Hugging Face and builds an in-memory index."""
        logger.info("🗺️ Loading Topological Knowledgebase from Hugging Face...")
        try:
            # Load the 'topology' configuration.
            # Hugging Face defaults uploaded JSONL files to the 'train' split.
            ds = load_dataset("IoT-Brain/TopoSense-Bench", "topology", split="train")

            for item in ds:
                # Normalize keys for easier matching (snake_case for building names)
                b_name = item['building'].lower().replace(" ", "_")
                floor = item['floor'].lower()
                content = item['content']

                if b_name not in self.topo_index:
                    self.topo_index[b_name] = {}

                self.topo_index[b_name][floor] = content

            logger.info(f"✅ Indexed {len(self.topo_index)} buildings.")
        except Exception as e:
            logger.error(f"❌ Failed to load topology: {e}")

    def retrieve_context(self, query):
        """
        A simple heuristic retriever.
        Identifies the relevant map file based on keywords in the query.
        This simulates the 'Topological Anchor' step in the IoT-Brain architecture.

        Args:
            query (str): The user's natural language query.

        Returns:
            str or None: The content of the specific floor plan if found, else None.
        """
        query_lower = query.lower()

        target_building = None
        target_floor = None

        # 1. Building Matching Logic
        # Iterate through all known building names in the index
        for b_name in self.topo_index.keys():
            # Replace underscores with spaces for natural language matching
            # (e.g., teaching_building_1 -> "teaching building 1")
            natural_name = b_name.replace("_", " ")
            if natural_name in query_lower:
                target_building = b_name
                break

        # 2. Floor Matching Logic
        # Handle common short formats: "1f", "2f"...
        floors = ["1f", "2f", "3f", "4f", "5f", "6f", "7f", "8f", "9f", "10f"]
        for f in floors:
            # Match variations like "1st floor", "2nd floor", "10th floor"
            digit = f[:-1]
            if (f in query_lower or
                f"{digit}st floor" in query_lower or
                f"{digit}nd floor" in query_lower or
                f"{digit}rd floor" in query_lower or
                f"{digit}th floor" in query_lower):
                target_floor = f.upper()  # Standardize to "1F"
                break

        # Map explicit natural language floor descriptions to standard format
        if "first floor" in query_lower: target_floor = "1F"
        if "second floor" in query_lower: target_floor = "2F"
        if "third floor" in query_lower: target_floor = "3F"
        if "fourth floor" in query_lower: target_floor = "4F"

        # 3. Retrieve and Return Map Content
        if target_building and target_floor:
            # Retrieve specific floor map from index
            floors_map = self.topo_index[target_building]
            # Try to match the key (case-insensitive)
            for key, content in floors_map.items():
                if key.lower() == target_floor.lower():
                    return f"Building: {target_building}, Floor: {target_floor}\n\n[Map Data]\n{content}"

        return None