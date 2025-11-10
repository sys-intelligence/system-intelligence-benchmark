import os
import sys

from sdk.logger import logger

if sys.version_info >= (3, 11):
    import tomllib as pytoml  # For Python 3.11+, use 'import tomllib' instead
else:
    # For Python 3.10 and earlier, use tomli
    # Note: tomli is not included in the standard library for Python 3.10
    # You may need to install it via pip: pip install tomli
    import tomli as pytoml  # For Python 3.10 and earlier, use 'import tomli'


def read_toml_config(config_path):
    """Read configuration from a TOML file."""
    try:
        with open(config_path, 'rb') as f:  # Opening in binary mode as required by tomli
            config_data = pytoml.load(f)
        return config_data
    except Exception as e:
        logger.info('Error reading TOML file: %s', e)
        return {}


def set_llm_endpoint_from_config(config_path):
    """Set LLM endpoint environment variables from the configuration dictionary."""
    logger.info('Read configuration from %s', config_path)
    config = read_toml_config(config_path)

    if not config:
        logger.info('Failed to load configuration from env.toml. Please check the file.')
        sys.exit(1)
    logger.info('Loaded configuration:')

    # Read all values in the llm section and set them as environment variables
    llm_config = config.get('llm', {})
    evaluator_config = config.get('evaluator_api_keys', {})

    # Validate evaluator_api_keys: if the section exists, all keys must have non-empty values
    if evaluator_config:
        empty_keys = [key for key, value in evaluator_config.items() if not value or str(value).strip() == '']
        if empty_keys:
            logger.error('Error: The following required API keys in [evaluator_api_keys] are empty:')
            for key in empty_keys:
                logger.error('  - %s', key)
            logger.error('[evaluator_api_keys] section indicates these are REQUIRED for the benchmark to run.')
            logger.error('Please provide valid API keys for all entries in [evaluator_api_keys].')
            sys.exit(1)

    # Detect conflicts between [llm] and [evaluator_api_keys]
    common_keys = set(llm_config.keys()) & set(evaluator_config.keys())
    if common_keys:
        conflicting_keys = []
        for key in common_keys:
            if llm_config[key] != evaluator_config[key]:
                conflicting_keys.append(key)

        if conflicting_keys:
            logger.warning('Warning: The following API keys are defined in both [llm] and [evaluator_api_keys] with different values:')
            for key in conflicting_keys:
                logger.warning('  - %s', key)
            logger.warning('Only [evaluator_api_keys] values will be used for both evaluator and model under test.')

    # First, set environment variables from [llm]
    logger.info('Setting the following environment variables from [llm]:')
    for key, value in llm_config.items():
        logger.info('%s', f'{key}: [REDACTED]' if 'key' in key.lower() else f'{key}: {value}')
        os.environ[key] = value
        # add exception for SWE-Agent:
        if key == 'AZURE_API_KEY':
            os.environ['AZURE_OPENAI_API_KEY'] = value
            logger.info('AZURE_OPENAI_API_KEY: [REDACTED]')

    # Then, set environment variables from [evaluator_api_keys] (will override [llm] if conflict)
    logger.info('Setting the following environment variables from [evaluator_api_keys]:')
    for key, value in evaluator_config.items():
        logger.info('%s', f'{key}: [REDACTED]' if 'key' in key.lower() else f'{key}: {value}')
        os.environ[key] = value
        # add exception for SWE-Agent:
        if key == 'AZURE_API_KEY':
            os.environ['AZURE_OPENAI_API_KEY'] = value
            logger.info('AZURE_OPENAI_API_KEY: [REDACTED]')
