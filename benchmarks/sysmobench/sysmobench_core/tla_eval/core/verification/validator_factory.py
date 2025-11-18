"""
Validator factory for different specification languages.

This module provides a factory function to create appropriate validators
based on the specification language (TLA+, Alloy, PAT, etc.).
"""

import logging
from typing import Union

logger = logging.getLogger(__name__)


def get_validator(language: str, timeout: int = 30) -> Union['TLAValidator', 'AlloyValidator']:
    """
    Get appropriate validator for the specification language.

    This factory function creates and returns the correct validator instance
    based on the target specification language.

    Args:
        language: Specification language ("tla", "TLA+", "alloy", "Alloy", "pat", "PAT")
        timeout: Validation timeout in seconds

    Returns:
        Validator instance (TLAValidator or AlloyValidator)

    Raises:
        ValueError: If the language is not supported

    Example:
        >>> validator = get_validator("alloy", timeout=60)
        >>> result = validator.validate(spec_content, output_dir)
    """
    # Normalize language name (lowercase, remove "+")
    language_normalized = language.lower().replace("+", "").strip()

    if language_normalized == "tla":
        from .validators import TLAValidator
        logger.debug(f"Creating TLAValidator with timeout={timeout}s")
        return TLAValidator(timeout=timeout)

    elif language_normalized == "alloy":
        from .alloy_validator import AlloyValidator
        logger.debug(f"Creating AlloyValidator with timeout={timeout}s")
        return AlloyValidator(timeout=timeout)

    elif language_normalized == "pat":
        # PAT support not yet implemented
        raise NotImplementedError(
            f"PAT language support is not yet implemented. "
            f"Currently supported: TLA+, Alloy"
        )
    else:
        raise ValueError(
            f"Unsupported specification language: '{language}'. "
            f"Supported languages: TLA+, Alloy"
        )


def get_supported_languages() -> list:
    """
    Get list of supported specification languages.

    Returns:
        List of supported language names
    """
    return ["TLA+", "Alloy"]


def is_language_supported(language: str) -> bool:
    """
    Check if a language is supported.

    Args:
        language: Language name to check

    Returns:
        True if supported, False otherwise
    """
    language_normalized = language.lower().replace("+", "").strip()
    return language_normalized in ["tla", "alloy"]
