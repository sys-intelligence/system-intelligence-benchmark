"""
TLC Error Classification Module

This module provides robust error classification for TLC model checker results,
based on TLC's internal error code system rather than brittle string matching.
"""

from enum import Enum
from typing import Dict, Optional, Tuple, List
from dataclasses import dataclass
import re

from .sany_error_code_reverse import SANYErrorCodeReverse, SANYErrorMatch


class TLCErrorCategory(Enum):
    """High-level categories of TLC errors"""
    SUCCESS = "success"
    VIOLATION_ASSUMPTION = "violation_assumption"
    VIOLATION_DEADLOCK = "violation_deadlock"
    VIOLATION_SAFETY = "violation_safety"
    VIOLATION_LIVENESS = "violation_liveness"
    VIOLATION_ASSERT = "violation_assert"
    FAILURE_SPEC_EVAL = "failure_spec_eval"
    FAILURE_SAFETY_EVAL = "failure_safety_eval"
    FAILURE_LIVENESS_EVAL = "failure_liveness_eval"
    ERROR_SPEC_PARSE = "error_spec_parse"
    ERROR_CONFIG_PARSE = "error_config_parse"
    ERROR_STATESPACE_TOO_LARGE = "error_statespace_too_large"
    ERROR_SYSTEM = "error_system"
    ERROR_UNKNOWN = "error_unknown"


@dataclass
class TLCErrorInfo:
    """Detailed information about a TLC error"""
    category: TLCErrorCategory
    exit_code: int
    error_code: Optional[int] = None
    message: str = ""
    description: str = ""
    is_compilation_error: bool = False
    is_runtime_error: bool = False
    is_violation: bool = False
    # SANY-specific fields
    sany_error_match: Optional[SANYErrorMatch] = None
    is_sany_error: bool = False


class TLCErrorClassifier:
    """
    Classifier for TLC model checker errors based on exit codes and output parsing.
    
    This provides a robust alternative to string matching by using TLC's
    structured error reporting system. For SANY errors, it uses pattern matching
    to reverse-engineer error codes from error messages.
    """
    
    # TLC exit codes from EC.ExitStatus
    EXIT_CODE_TO_CATEGORY = {
        0: TLCErrorCategory.SUCCESS,
        10: TLCErrorCategory.VIOLATION_ASSUMPTION,
        11: TLCErrorCategory.VIOLATION_DEADLOCK,
        12: TLCErrorCategory.VIOLATION_SAFETY,
        13: TLCErrorCategory.VIOLATION_LIVENESS,
        14: TLCErrorCategory.VIOLATION_ASSERT,
        75: TLCErrorCategory.FAILURE_SPEC_EVAL,
        76: TLCErrorCategory.FAILURE_SAFETY_EVAL,
        77: TLCErrorCategory.FAILURE_LIVENESS_EVAL,
        150: TLCErrorCategory.ERROR_SPEC_PARSE,
        151: TLCErrorCategory.ERROR_CONFIG_PARSE,
        152: TLCErrorCategory.ERROR_STATESPACE_TOO_LARGE,
        153: TLCErrorCategory.ERROR_SYSTEM,
        # SANY exit codes (SANY parser errors with -error-codes)
        2: TLCErrorCategory.ERROR_SPEC_PARSE,   # SANY parsing error
        4: TLCErrorCategory.ERROR_SPEC_PARSE,   # SANY semantic analysis error
        255: TLCErrorCategory.ERROR_SPEC_PARSE,  # SANY parsing error (legacy)
        1: TLCErrorCategory.ERROR_SPEC_PARSE,    # Generic SANY error (legacy)
        # System-level exit codes
        -1: TLCErrorCategory.ERROR_SYSTEM,      # JVM crash, signal termination, or system-level error
    }
    
    # TLC internal error codes (from EC.java)
    ERROR_CODE_DESCRIPTIONS = {
        # Violations
        2102: ("Initial state error", "TLC_INITIAL_STATE"),
        2104: ("Assumption false", "TLC_ASSUMPTION_FALSE"),
        2105: ("Assumption evaluation error", "TLC_ASSUMPTION_EVALUATION_ERROR"),
        2107: ("Invariant violated in initial state", "TLC_INVARIANT_VIOLATED_INITIAL"),
        2110: ("Invariant violated during behavior", "TLC_INVARIANT_VIOLATED_BEHAVIOR"),
        2111: ("Invariant evaluation failed", "TLC_INVARIANT_EVALUATION_FAILED"),
        2112: ("Action property violated", "TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR"),
        2114: ("Deadlock reached", "TLC_DEADLOCK_REACHED"),
        2116: ("Temporal property violated", "TLC_TEMPORAL_PROPERTY_VIOLATED"),
        2132: ("Assert failed", "TLC_VALUE_ASSERT_FAILED"),
        
        # Evaluation failures
        2103: ("Nested expression error", "TLC_NESTED_EXPRESSION"),
        2109: ("Next state not completely specified", "TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT"),
        2115: ("States exist but no next actions", "TLC_STATES_AND_NO_NEXT_ACTION"),
        2147: ("Fingerprint exception", "TLC_FINGERPRINT_EXCEPTION"),
        
        # Parse errors
        2171: ("TLA+ parsing failed", "TLC_PARSING_FAILED2"),
        3002: ("TLA+ parsing failed", "TLC_PARSING_FAILED"),
        
        # Config errors
        2222: ("Value not assigned to constant parameter", "TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM"),
        2226: ("Identifier does not appear in specification", "TLC_CONFIG_ID_DOES_NOT_APPEAR_IN_SPEC"),
        2231: ("Missing INIT in configuration", "TLC_CONFIG_MISSING_INIT"),
        2232: ("Missing NEXT in configuration", "TLC_CONFIG_MISSING_NEXT"),
        
        # System errors
        1001: ("System out of memory", "SYSTEM_OUT_OF_MEMORY"),
        1005: ("System stack overflow", "SYSTEM_STACK_OVERFLOW"),
        2125: ("Error reading pool", "SYSTEM_ERROR_READING_POOL"),
        2127: ("Error writing pool", "SYSTEM_ERROR_WRITING_POOL"),
    }
    
    def __init__(self):
        """Initialize the TLC error classifier with SANY error reverse mapping."""
        self.sany_classifier = SANYErrorCodeReverse()
    
    def classify_tlc_result(self, exit_code: int, stdout: str = "", stderr: str = "") -> TLCErrorInfo:
        """
        Classify TLC execution result based on exit code and output.
        
        Args:
            exit_code: TLC process exit code
            stdout: Standard output from TLC
            stderr: Standard error from TLC
            
        Returns:
            TLCErrorInfo with detailed classification
        """
        # First, try to get category from exit code
        category = self.EXIT_CODE_TO_CATEGORY.get(exit_code, TLCErrorCategory.ERROR_UNKNOWN)
        
        # Initialize SANY-specific variables
        sany_error_match = None
        is_sany_error = False
        
        # Extract error code from output if available
        error_code = self._extract_error_code(stdout, stderr)
        
        # Handle SANY errors (exit codes: 1, 2, 4, 255) with pattern matching
        if exit_code in [1, 2, 4, 255] and category == TLCErrorCategory.ERROR_SPEC_PARSE:
            combined_output = stdout + stderr
            sany_error_match = self.sany_classifier.classify_sany_error(combined_output)
            if sany_error_match:
                is_sany_error = True
                error_code = sany_error_match.error_code
                # Override description with SANY-specific description
        
        # Get detailed description
        description = ""
        if sany_error_match:
            description = sany_error_match.description
        elif error_code and error_code in self.ERROR_CODE_DESCRIPTIONS:
            description = self.ERROR_CODE_DESCRIPTIONS[error_code][0]
        
        # Determine error characteristics
        is_compilation_error = category in [
            TLCErrorCategory.ERROR_SPEC_PARSE,
            TLCErrorCategory.ERROR_CONFIG_PARSE
        ]
        
        is_runtime_error = category in [
            TLCErrorCategory.FAILURE_SPEC_EVAL,
            TLCErrorCategory.FAILURE_SAFETY_EVAL,
            TLCErrorCategory.FAILURE_LIVENESS_EVAL,
            TLCErrorCategory.ERROR_STATESPACE_TOO_LARGE,
            TLCErrorCategory.ERROR_SYSTEM
        ]
        
        is_violation = category in [
            TLCErrorCategory.VIOLATION_ASSUMPTION,
            TLCErrorCategory.VIOLATION_DEADLOCK,
            TLCErrorCategory.VIOLATION_SAFETY,
            TLCErrorCategory.VIOLATION_LIVENESS,
            TLCErrorCategory.VIOLATION_ASSERT
        ]
        
        # Extract message from output
        message = self._extract_error_message(stdout, stderr)
        
        return TLCErrorInfo(
            category=category,
            exit_code=exit_code,
            error_code=error_code,
            message=message,
            description=description,
            is_compilation_error=is_compilation_error,
            is_runtime_error=is_runtime_error,
            is_violation=is_violation,
            sany_error_match=sany_error_match,
            is_sany_error=is_sany_error
        )
    
    def _extract_error_code(self, stdout: str, stderr: str) -> Optional[int]:
        """Extract TLC internal error code from output."""
        combined_output = stdout + stderr
        
        # Look for TLC error code patterns
        # Pattern 1: @!@!@STARTMSG 2110:0 @!@!@
        pattern1 = r'@!@!@STARTMSG (\d+):\d+ @!@!@'
        matches = re.findall(pattern1, combined_output)
        if matches:
            # Return the last (most recent) error code
            return int(matches[-1])
        
        # Pattern 2: Error code in error messages
        pattern2 = r'Error:\s*(\d{4})'
        matches = re.findall(pattern2, combined_output)
        if matches:
            return int(matches[-1])
        
        return None
    
    def _extract_error_message(self, stdout: str, stderr: str) -> str:
        """Extract human-readable error message from TLC output."""
        combined_output = stdout + stderr
        
        # Look for common error message patterns
        error_patterns = [
            r'Error:\s*(.+?)(?:\n|$)',
            r'Invariant .+ is violated',
            r'Deadlock reached',
            r'The following formula is not valid',
            r'TLC found an error'
        ]
        
        for pattern in error_patterns:
            match = re.search(pattern, combined_output, re.IGNORECASE | re.MULTILINE)
            if match:
                return match.group(0).strip()
        
        # If no specific pattern found, return first non-empty line from stderr
        if stderr.strip():
            lines = stderr.strip().split('\n')
            for line in lines:
                if line.strip() and not line.startswith('@!@!@'):
                    return line.strip()
        
        return ""
    
    def get_error_statistics(self, results: List[TLCErrorInfo]) -> Dict[str, int]:
        """
        Get statistics on error categories from a list of TLC results.
        
        Args:
            results: List of TLCErrorInfo objects
            
        Returns:
            Dictionary with error category counts
        """
        stats = {category.value: 0 for category in TLCErrorCategory}
        
        for result in results:
            stats[result.category.value] += 1
        
        # Add aggregate counts
        stats['total_compilation_errors'] = sum(
            1 for r in results if r.is_compilation_error
        )
        stats['total_runtime_errors'] = sum(
            1 for r in results if r.is_runtime_error
        )
        stats['total_violations'] = sum(
            1 for r in results if r.is_violation
        )
        stats['total_successes'] = sum(
            1 for r in results if r.category == TLCErrorCategory.SUCCESS
        )
        
        return stats
    
    def is_fixable_error(self, error_info: TLCErrorInfo) -> bool:
        """
        Determine if an error is potentially fixable by modifying the specification.
        
        Args:
            error_info: TLC error information
            
        Returns:
            True if error might be fixable by spec changes
        """
        # Parse errors and config errors are often fixable
        if error_info.is_compilation_error:
            return True
        
        # Some runtime errors are fixable
        fixable_categories = {
            TLCErrorCategory.FAILURE_SPEC_EVAL,
            TLCErrorCategory.FAILURE_SAFETY_EVAL,
            TLCErrorCategory.ERROR_STATESPACE_TOO_LARGE,
        }
        
        return error_info.category in fixable_categories
    
    def suggest_fixes(self, error_info: TLCErrorInfo) -> List[str]:
        """
        Suggest potential fixes for common TLC errors.
        
        Args:
            error_info: TLC error information
            
        Returns:
            List of suggested fixes
        """
        suggestions = []
        
        if error_info.category == TLCErrorCategory.ERROR_SPEC_PARSE:
            suggestions.extend([
                "Check TLA+ syntax for missing operators or malformed expressions",
                "Verify module names match file names",
                "Check for proper EXTENDS declarations"
            ])
        elif error_info.category == TLCErrorCategory.ERROR_CONFIG_PARSE:
            suggestions.extend([
                "Check .cfg file syntax",
                "Verify all constants are defined",
                "Ensure INIT and NEXT are specified"
            ])
        elif error_info.category == TLCErrorCategory.FAILURE_SPEC_EVAL:
            suggestions.extend([
                "Check for undefined variables or constants",
                "Verify state predicates are properly formed",
                "Look for type errors in expressions"
            ])
        elif error_info.category == TLCErrorCategory.ERROR_STATESPACE_TOO_LARGE:
            suggestions.extend([
                "Reduce model parameters or state space",
                "Add state constraints",
                "Use symmetry to reduce state space"
            ])
        elif error_info.is_violation:
            suggestions.extend([
                "This is a model violation, not an error",
                "Check if the violation is expected",
                "Verify invariants and properties are correctly specified"
            ])
        
        return suggestions


# Convenience function
def classify_tlc_result(exit_code: int, stdout: str = "", stderr: str = "") -> TLCErrorInfo:
    """Classify TLC result using default classifier."""
    classifier = TLCErrorClassifier()
    return classifier.classify_tlc_result(exit_code, stdout, stderr)