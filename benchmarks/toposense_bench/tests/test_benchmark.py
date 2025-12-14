"""Unit tests for TopoSense-Bench."""

import unittest
from datasets import load_dataset


class TestTopoSenseBench(unittest.TestCase):
    """Test suite for TopoSense-Bench data connectivity and integrity."""

    def test_hf_connection(self):
        """
        Test if we can connect to Hugging Face, authenticate (if needed),
        and stream the first data sample successfully.
        """
        try:
            # Load the dataset in streaming mode to avoid downloading the entire file.
            # Note: Using 'train' split as per default Hugging Face JSONL behavior.
            dataset = load_dataset(
                "IoT-Brain/TopoSense-Bench",
                "queries",
                split="train",
                streaming=True
            )

            # Retrieve the first item to verify data access
            first_item = next(iter(dataset))
            
            print(f"Successfully loaded item category: {first_item.get('category', 'Unknown')}")

            # Assert that essential fields are present in the data
            self.assertTrue('query' in first_item, "Field 'query' is missing.")
            self.assertTrue('answer' in first_item, "Field 'answer' is missing.")
            self.assertTrue('category' in first_item, "Field 'category' is missing.")

        except Exception as e:
            self.fail(f"Failed to load dataset from Hugging Face: {e}")


if __name__ == '__main__':
    unittest.main()