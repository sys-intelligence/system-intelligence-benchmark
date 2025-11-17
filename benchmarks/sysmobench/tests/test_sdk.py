"""Test SDK integration for SysMoBench.

This module tests that SysMoBench can properly integrate with the SDK.
We only test SDK features that SysMoBench actually uses.
"""

import sys
from pathlib import Path

# Add SDK to path (following other benchmarks' pattern)
SDK_ROOT = Path(__file__).parent.parent.parent.parent
sys.path.insert(0, str(SDK_ROOT))

from sdk.utils import set_llm_endpoint_from_config


def test_config_loading():
    """Test that we can load env.toml configuration file.

    This is critical because SysMoBench uses set_llm_endpoint_from_config
    to configure LLM API endpoints for TLA+ generation.
    """
    config_path = Path(__file__).parent.parent / 'env.toml'
    # Should not raise exception
    set_llm_endpoint_from_config(str(config_path))
