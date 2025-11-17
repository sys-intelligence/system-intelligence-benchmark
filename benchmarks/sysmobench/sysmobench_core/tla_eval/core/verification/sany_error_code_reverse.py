"""
SANY Error Code Reverse Mapping Module

This module provides reverse mapping from SANY error messages to internal error codes.
Since SANY (TLA+ Semantic Analyzer) doesn't output structured error codes like TLC,
we use pattern matching on error messages to infer the original error codes.

Based on TLA+ source code from:
- tla2sany/semantic/ErrorCode.java (error code definitions)
- tla2sany/semantic/Generator.java (error message generation)
"""

import re
from typing import Optional, Tuple, Dict, List
from dataclasses import dataclass
from enum import Enum


@dataclass
class SANYErrorMatch:
    """Result of SANY error code matching"""
    error_code: int
    error_name: str
    confidence: float  # 0.0 to 1.0
    matched_pattern: str
    description: str


class SANYErrorCategory(Enum):
    """SANY error categories based on error code ranges"""
    PARSER_INTERNAL = "parser_internal"      # 4000-4002
    INTERNAL_ERROR = "internal_error"        # 4003-4005  
    BASIC_SEMANTIC = "basic_semantic"        # 4200-4206
    MODULE_IMPORT = "module_import"          # 4220-4224
    INSTANCE_SUBSTITUTION = "instance_substitution"  # 4240-4247
    FUNCTION_RECORD = "function_record"      # 4260-4262
    HIGHER_ORDER = "higher_order"           # 4270-4275
    RECURSIVE = "recursive"                 # 4290-4294
    TEMPORAL = "temporal"                   # 4310-4315
    LABEL = "label"                         # 4330-4337
    PROOF = "proof"                         # 4350-4362
    WARNING = "warning"                     # 4800+
    SYNTAX_PARSE = "syntax_parse"           # 9000+ (custom for common parse errors)


class SANYErrorCodeReverse:
    """
    Reverse engineer SANY error codes from error messages.
    
    This class contains pattern matching rules to identify SANY internal
    error codes based on the error message text, since SANY doesn't output
    structured error codes like TLC does.
    """
    
    def __init__(self):
        self._error_patterns = self._build_error_patterns()
    
    def _build_error_patterns(self) -> Dict[int, Tuple[str, str, str]]:
        """
        Build pattern matching rules for SANY error codes.
        
        Returns:
            Dict mapping error_code -> (pattern, error_name, description)
        """
        patterns = {
            # SANY Basic Semantic Errors (4200-4206)
            # Reference: Generator.java:3304 "Unknown operator: `" + selectorItemToString(sel, eidx) + "'."
            4200: (
                r"Unknown operator",
                "SYMBOL_UNDEFINED", 
                "Symbol or operator not defined"
            ),
            # Reference: SymbolTable.java:164 "Multiply-defined symbol '" + name + "': this definition or declaration conflicts"
            # Reference: Generator.java "Operator " + name.toString() + " already defined or declared."
            # Reference: Generator.java "Function name `" + name.toString() + "' already defined or declared."
            4201: (
                r"(?:Multiply-defined.*symbol|already.*defined.*declared|defined.*declared)",
                "SYMBOL_REDEFINED",
                "Symbol redefined in same scope"
            ),
            # Reference: SymbolTable.java:148 "Symbol " + name + " is a built-in operator, and cannot be redefined."
            4202: (
                r"(?:built-in.*operator.*cannot.*redefined|built-in.*cannot.*redefined)",
                "BUILT_IN_SYMBOL_REDEFINED",
                "Built-in TLA+ operator redefined"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4203: (
                r"(?:name.*incomplete|incomplete.*name|operator.*name.*incomplete)",
                "OPERATOR_NAME_INCOMPLETE", 
                "Operator name syntax incomplete"
            ),
            # Reference: Generator.java "The operator " + curName.toString() + " requires " + (nodeArity - opDefArityFound) + " arguments."
            4204: (
                r"(?:operator.*requires.*argument|requires.*argument)",
                "OPERATOR_GIVEN_INCORRECT_NUMBER_OF_ARGUMENTS",
                "Operator called with wrong number of arguments"
            ),
            # Reference: OpApplNode.java "Level error in applying operator" + "The level of argument" + "exceeds the maximum level allowed"
            4205: (
                r"(?:Level.*error.*applying.*operator|level.*argument.*exceed.*maximum|level.*constraint)",
                "OPERATOR_LEVEL_CONSTRAINTS_EXCEEDED",
                "TLA+ level constraint violated"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4206: (
                r"(?:Assumption.*not.*constant|is.*not.*constant|not.*constant)",
                "ASSUMPTION_IS_NOT_CONSTANT",
                "Assumption must be constant-level"
            ),
            
            # SANY Module Import Errors (4220-4224)
            # Reference: SpecObj.java "Cannot find source file for module " + name + " imported in module"
            4220: (
                r"Cannot.*find.*source.*file.*module",
                "MODULE_FILE_CANNOT_BE_FOUND",
                "Module file not found"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4221: (
                r"(?:does.*not.*match.*name.*module|name.*different.*file)",
                "MODULE_NAME_DIFFERENT_FROM_FILE_NAME",
                "Module name doesn't match filename"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4222: (
                r"(?:dependencies.*circular|circular.*dependencies|circular.*module)",
                "MODULE_DEPENDENCIES_ARE_CIRCULAR",
                "Circular module dependencies detected"
            ),
            # Reference: SymbolTable.java:244 "Multiply-defined module '" + name + "': this definition or declaration conflicts"
            4223: (
                r"(?:Multiply-defined.*module|Module.*redefined|module.*already.*defined)",
                "MODULE_REDEFINED",
                "Module defined multiple times"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4224: (
                r"(?:Extended.*module.*symbol.*unification.*conflict|symbol.*unification.*conflict|unification.*conflict)",
                "EXTENDED_MODULES_SYMBOL_UNIFICATION_CONFLICT",
                "Symbol conflict in extended modules"
            ),
            
            # SANY Function and Record Errors (4260-4262)
            # Reference: Generator.java "Function '" + name + "' is defined with " + numParms + " parameters, but is applied to " + numArgs + " arguments."
            4260: (
                r"(?:Function.*defined.*parameter.*applied.*argument|Function.*wrong.*number|applied.*argument)",
                "FUNCTION_GIVEN_INCORRECT_NUMBER_OF_ARGUMENTS",
                "Function called with wrong number of arguments"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4261: (
                r"(?:EXCEPT.*undefined|Function.*EXCEPT.*undefined|EXCEPT.*used.*undefined)",
                "FUNCTION_EXCEPT_AT_USED_WHERE_UNDEFINED",
                "EXCEPT used where function undefined"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4262: (
                r"(?:Record.*field.*defined.*multiple|Record.*field.*redefined|field.*redefined|field.*multiple)",
                "RECORD_CONSTRUCTOR_FIELD_REDEFINITION", 
                "Record field defined multiple times"
            ),
            
            # SANY Instance Substitution Errors (4240-4247) 
            # Reference: Need to find this pattern in TLA+ source
            4240: (
                r"(?:missing.*symbol|symbol.*missing)",
                "INSTANCE_SUBSTITUTION_MISSING_SYMBOL",
                "Required substitution symbol missing"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4241: (
                r"(?:symbol.*redefined.*multiple|symbol.*defined.*multiple|redefined.*multiple)",
                "INSTANCE_SUBSTITUTION_SYMBOL_REDEFINED_MULTIPLE_TIMES",
                "Substitution symbol redefined multiple times"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4242: (
                r"(?:illegal.*symbol.*redefinition|illegal.*redefinition)",
                "INSTANCE_SUBSTITUTION_ILLEGAL_SYMBOL_REDEFINITION",
                "Illegal symbol redefinition in substitution"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4243: (
                r"(?:incorrect.*arity|arity.*incorrect)",
                "INSTANCE_SUBSTITUTION_OPERATOR_CONSTANT_INCORRECT_ARITY",
                "Operator/constant arity mismatch in substitution"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4244: (
                r"(?:non-Leibniz.*operator|Leibniz.*operator)",
                "INSTANCE_SUBSTITUTION_NON_LEIBNIZ_OPERATOR",
                "Non-Leibniz operator in substitution"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4245: (
                r"(?:level.*constraint.*exceeded|constraint.*exceeded)",
                "INSTANCE_SUBSTITUTION_LEVEL_CONSTRAINTS_EXCEEDED",
                "Level constraints exceeded in substitution"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4246: (
                r"(?:level.*constraint.*not.*met|constraint.*not.*met)",
                "INSTANCE_SUBSTITUTION_LEVEL_CONSTRAINT_NOT_MET",
                "Level constraint not met in substitution"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4247: (
                r"(?:coparameter.*level.*constraint.*exceeded|coparameter.*exceeded)",
                "INSTANCE_SUBSTITUTION_COPARAMETER_LEVEL_CONSTRAINTS_EXCEEDED",
                "Coparameter level constraints exceeded"
            ),
            
            # SANY Higher-Order Operator Errors (4270-4275)
            # Reference: Need to find this pattern in TLA+ source
            4270: (
                r"(?:Higher-order.*operator.*required.*expression.*given|operator.*required.*expression)",
                "HIGHER_ORDER_OPERATOR_REQUIRED_BUT_EXPRESSION_GIVEN",
                "Expression given where higher-order operator required"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4271: (
                r"(?:Expected.*arity.*but.*found|Argument.*should.*parameter.*operator|arity.*incorrect)",
                "HIGHER_ORDER_OPERATOR_ARGUMENT_HAS_INCORRECT_ARITY",
                "Higher-order operator argument has incorrect arity"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4272: (
                r"(?:parameter.*level.*constraint.*not.*met|level.*constraint.*not.*met)",
                "HIGHER_ORDER_OPERATOR_PARAMETER_LEVEL_CONSTRAINT_NOT_MET",
                "Parameter level constraint not met"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4273: (
                r"(?:coparameter.*level.*constraint.*exceeded|coparameter.*exceeded)",
                "HIGHER_ORDER_OPERATOR_COPARAMETER_LEVEL_CONSTRAINTS_EXCEEDED",
                "Coparameter level constraints exceeded"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4274: (
                r"(?:Selector.*argument.*LAMBDA.*expression|LAMBDA.*argument.*arity)",
                "LAMBDA_OPERATOR_ARGUMENT_HAS_INCORRECT_ARITY",
                "LAMBDA operator argument has incorrect arity"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4275: (
                r"(?:Lambda.*given.*where.*expression.*required|Lambda.*expression.*required)",
                "LAMBDA_GIVEN_WHERE_EXPRESSION_REQUIRED",
                "Lambda given where expression required"
            ),
            
            # SANY Recursive Operator Errors (4290-4294)
            # Reference: Need to find this pattern in TLA+ source
            4290: (
                r"(?:Recursive.*operator.*primed.*parameter|primed.*parameter)",
                "RECURSIVE_OPERATOR_PRIMES_PARAMETER",
                "Recursive operator has primed parameter"
            ),
            # Reference: Generator.java "Symbol " + odn.getName().toString() + " declared in RECURSIVE statement but not defined."
            4291: (
                r"(?:declared.*RECURSIVE.*not.*defined|Recursive.*operator.*declared.*not.*defined|declared.*not.*defined)",
                "RECURSIVE_OPERATOR_DECLARED_BUT_NOT_DEFINED",
                "Recursive operator declared but not defined"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4292: (
                r"(?:Recursive.*operator.*arity.*mismatch|arity.*mismatch|declaration.*definition.*arity)",
                "RECURSIVE_OPERATOR_DECLARATION_DEFINITION_ARITY_MISMATCH",
                "Recursive operator declaration/definition arity mismatch"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4293: (
                r"(?:Recursive.*operator.*defined.*wrong.*LET.*level|defined.*wrong.*level|wrong.*LET.*level)",
                "RECURSIVE_OPERATOR_DEFINED_IN_WRONG_LET_IN_LEVEL",
                "Recursive operator defined at wrong LET-IN level"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4294: (
                r"(?:Recursive.*section.*illegal.*definition|illegal.*definition.*recursive|illegal.*definition)",
                "RECURSIVE_SECTION_CONTAINS_ILLEGAL_DEFINITION",
                "Illegal definition in recursive section"
            ),
            
            # SANY Temporal Operator Errors (4310-4315) - Updated to match actual TLA+ source
            # Reference: OpApplNode.java "[] followed by action not of form [A]_v."
            4310: (
                r"(?:\[\].*followed.*action.*not.*form.*\[A\]_v|followed.*action.*not.*form)",
                "ALWAYS_PROPERTY_SENSITIVE_TO_STUTTERING",
                "[] followed by action not of form [A]_v"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4311: (
                r"(?:<>.*followed.*action.*not.*form|followed.*action.*not.*form)",
                "EVENTUALLY_PROPERTY_SENSITIVE_TO_STUTTERING",
                "<> followed by action not of form <<A>>_v"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4312: (
                r"(?:Binary.*temporal.*operator.*action.*level|Action.*used.*where.*temporal.*formula|temporal.*operator.*action)",
                "BINARY_TEMPORAL_OPERATOR_WITH_ACTION_LEVEL_PARAMETER",
                "Action used where temporal/state formula required"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4313: (
                r"(?:Logical.*operator.*mixed.*action.*temporal|mixed.*action.*temporal)",
                "LOGICAL_OPERATOR_WITH_MIXED_ACTION_TEMPORAL_PARAMETERS",
                "Logical operator with mixed action/temporal parameters"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4314: (
                r"(?:Quantified.*temporal.*formula.*action.*level.*bound|temporal.*formula.*action.*bound)",
                "QUANTIFIED_TEMPORAL_FORMULA_WITH_ACTION_LEVEL_BOUND",
                "Quantified temporal formula with action-level bound"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4315: (
                r"(?:Quantification.*temporal.*level.*bound|temporal.*level.*bound)",
                "QUANTIFICATION_WITH_TEMPORAL_LEVEL_BOUND",
                "Quantification with temporal-level bound"
            ),
            
            # SANY Label Errors (4330-4337)
            # Reference: Generator.java "Repeated formal parameter " + odns[i].getName().toString() + " \nin label `" + ln.getName().toString() + "'."
            4330: (
                r"(?:Repeated.*formal.*parameter.*label|Label.*parameter.*repeated|repeated.*parameter)",
                "LABEL_PARAMETER_REPETITION",
                "Label parameter repeated"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4331: (
                r"(?:Label.*parameter.*missing|parameter.*missing)",
                "LABEL_PARAMETER_MISSING",
                "Required label parameter missing"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4332: (
                r"(?:Label.*parameter.*unnecessary|parameter.*unnecessary)",
                "LABEL_PARAMETER_UNNECESSARY",
                "Unnecessary label parameter provided"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4333: (
                r"(?:Label.*not.*definition.*proof.*step|not.*definition.*step)",
                "LABEL_NOT_IN_DEFINITION_OR_PROOF_STEP",
                "Label not in definition or proof step"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4334: (
                r"(?:Label.*not.*allowed.*nested.*ASSUME.*PROVE|not.*allowed.*ASSUME.*PROVE)",
                "LABEL_NOT_ALLOWED_IN_NESTED_ASSUME_PROVE_WITH_NEW",
                "Label not allowed in nested ASSUME PROVE with NEW"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4335: (
                r"(?:Label.*not.*allowed.*function.*EXCEPT|not.*allowed.*EXCEPT)",
                "LABEL_NOT_ALLOWED_IN_FUNCTION_EXCEPT",
                "Label not allowed in function EXCEPT"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4336: (
                r"(?:Label.*already.*defined|Label.*redefined|already.*defined|redefined)",
                "LABEL_REDEFINITION",
                "Label redefined"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4337: (
                r"(?:Label.*given.*wrong.*number.*argument|wrong.*number.*argument)",
                "LABEL_GIVEN_INCORRECT_NUMBER_OF_ARGUMENTS",
                "Label given wrong number of arguments"
            ),
            
            # SANY Proof-related Errors (4350-4357)
            # Reference: Need to find this pattern in TLA+ source
            4350: (
                r"(?:Proof.*step.*implicit.*level.*cannot.*name|implicit.*level.*cannot.*name)",
                "PROOF_STEP_WITH_IMPLICIT_LEVEL_CANNOT_HAVE_NAME",
                "Proof step with implicit level cannot have name"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4351: (
                r"(?:Non-expression.*used.*expression|expression.*used.*expression)",
                "PROOF_STEP_NON_EXPRESSION_USED_AS_EXPRESSION",
                "Non-expression used as expression in proof step"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4352: (
                r"(?:Temporal.*proof.*goal.*non-constant.*(?:TAKE|WITNESS|HAVE)|proof.*goal.*non-constant)",
                "TEMPORAL_PROOF_GOAL_WITH_NON_CONSTANT_TAKE_WITNESS_HAVE",
                "Temporal proof goal with non-constant TAKE/WITNESS/HAVE"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4353: (
                r"(?:Temporal.*proof.*goal.*non-constant.*CASE|proof.*goal.*CASE)",
                "TEMPORAL_PROOF_GOAL_WITH_NON_CONSTANT_CASE",
                "Temporal proof goal with non-constant CASE"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4354: (
                r"(?:Quantified.*temporal.*PICK.*formula.*non-constant.*bound|temporal.*formula.*non-constant)",
                "QUANTIFIED_TEMPORAL_PICK_FORMULA_WITH_NON_CONSTANT_BOUND",
                "Quantified temporal PICK formula with non-constant bound"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4355: (
                r"(?:ASSUME.*PROVE.*used.*where.*expression.*required|ASSUME.*PROVE.*expression)",
                "ASSUME_PROVE_USED_WHERE_EXPRESSION_REQUIRED",
                "ASSUME/PROVE used where expression required"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4356: (
                r"(?:ASSUME.*PROVE.*NEW.*constant.*temporal.*level.*bound|NEW.*constant.*temporal)",
                "ASSUME_PROVE_NEW_CONSTANT_HAS_TEMPORAL_LEVEL_BOUND",
                "ASSUME/PROVE NEW constant has temporal level bound"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4357: (
                r"(?:USE.*HIDE.*fact.*not.*valid|HIDE.*fact.*not.*valid|fact.*not.*valid)",
                "USE_OR_HIDE_FACT_NOT_VALID",
                "USE or HIDE fact not valid"
            ),
            
            # SANY Internal Errors (4003-4005)
            4003: (
                r"Internal\s+error",
                "INTERNAL_ERROR",
                "Internal SANY error"
            ),
            4004: (
                r"Suspected\s+unreachable\s+(?:code\s+)?check",
                "SUSPECTED_UNREACHABLE_CHECK",
                "Suspected unreachable code check failed"
            ),
            4005: (
                r"Unsupported\s+language\s+feature",
                "UNSUPPORTED_LANGUAGE_FEATURE",
                "Unsupported TLA+ language feature"
            ),
            
            # SANY Syntax/Parse Errors (Common but not in official ErrorCode.java)
            # These are parser-level errors that SANY reports but don't have official error codes
            # Reference: Need to find these patterns in TLA+ parser source
            9001: (
                r"(?:not.*properly.*indented|indented.*conjunction|indented.*disjunction|indented)",
                "INDENTATION_ERROR",
                "Improper indentation in conjunction/disjunction"
            ),
            # Reference: Need to find this pattern in TLA+ source
            9002: (
                r"(?:Precedence.*conflict.*ops|precedence.*conflict)",
                "OPERATOR_PRECEDENCE_CONFLICT",
                "Operator precedence conflict"
            ),
            # Reference: Need to find this pattern in TLA+ source
            9003: (
                r"(?:Encountered.*line|Unexpected.*token|Parse.*Error|unexpected)",
                "UNEXPECTED_TOKEN",
                "Unexpected token encountered"
            ),
            # Reference: Need to find this pattern in TLA+ source
            9004: (
                r"(?:Was.*expecting|expecting.*token|expecting)",
                "EXPECTED_TOKEN_MISSING",
                "Expected token missing"
            ),
            # Reference: Need to find this pattern in TLA+ source
            9005: (
                r"(?:follow.*each.*other.*without.*intervening.*operator|without.*intervening.*operator|missing.*operator)",
                "MISSING_OPERATOR",
                "Missing operator between expressions"
            ),
            # Reference: Need to find this pattern in TLA+ source
            9006: (
                r"(?:Fatal.*error.*parsing|Parse.*Error|Could.*not.*parse|parsing.*error)",
                "GENERAL_PARSE_ERROR",
                "General TLA+ parsing error"
            ),
            
            # Special unknown error code for fallback classification
            9999: (
                r".*",  # Matches any string as last resort
                "UNKNOWN_SANY_ERROR",
                "Unmatched SANY error requiring pattern analysis"
            ),
            
            # SANY Warnings (4800+)
            # Reference: Need to find this pattern in TLA+ source
            4800: (
                r"(?:Extended.*module.*symbol.*unification.*ambiguity|symbol.*unification.*ambiguity)",
                "EXTENDED_MODULES_SYMBOL_UNIFICATION_AMBIGUITY",
                "Symbol unification ambiguity in extended modules"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4801: (
                r"(?:Instanced.*module.*symbol.*unification.*ambiguity|module.*symbol.*unification.*ambiguity|unification.*ambiguity)",
                "INSTANCED_MODULES_SYMBOL_UNIFICATION_AMBIGUITY", 
                "Symbol unification ambiguity in instanced modules"
            ),
            # Reference: Need to find this pattern in TLA+ source
            4802: (
                r"(?:Record.*constructor.*field.*name.*clash|field.*name.*clash|name.*clash)",
                "RECORD_CONSTRUCTOR_FIELD_NAME_CLASH",
                "Record constructor field name clash"
            ),
        }
        
        return patterns
    
    def classify_sany_error(self, error_message: str) -> Optional[SANYErrorMatch]:
        """
        Classify SANY error message and return matching error code.
        
        Args:
            error_message: Error message text from SANY
            
        Returns:
            SANYErrorMatch if pattern matches, None otherwise
        """
        if not error_message or not error_message.strip():
            return None
        
        # Try to match each pattern
        best_match = None
        best_confidence = 0.0
        
        for error_code, (pattern, error_name, description) in self._error_patterns.items():
            match = re.search(pattern, error_message, re.IGNORECASE | re.MULTILINE)
            if match:
                # Calculate confidence based on pattern specificity
                confidence = self._calculate_confidence(pattern, match, error_message)
                
                if confidence > best_confidence:
                    best_confidence = confidence
                    best_match = SANYErrorMatch(
                        error_code=error_code,
                        error_name=error_name,
                        confidence=confidence,
                        matched_pattern=pattern,
                        description=description
                    )
        
        # If we found a high-confidence match, return it
        if best_match and best_confidence > 0.6:
            return best_match
        
        # FALLBACK: If no patterns matched with sufficient confidence, 
        # create an UNKNOWN error classification for debugging
        import logging
        logger = logging.getLogger(__name__)
        
        logger.warning(f"SANY Error Classification Failed - Unknown Error Pattern")
        logger.warning(f"Full error message content: {repr(error_message)}")
        
        # Return unknown error classification to ensure we don't lose the error
        return SANYErrorMatch(
            error_code=9999,  # Special code for unknown SANY errors
            error_name="UNKNOWN_SANY_ERROR",
            confidence=0.5,  # Medium confidence since we know it's an error, just don't know the type
            matched_pattern="<unmatched>",
            description="Unmatched SANY error - needs pattern analysis"
        )
    
    def _calculate_confidence(self, pattern: str, match: re.Match, full_message: str) -> float:
        """
        Calculate confidence score for a pattern match.
        
        Args:
            pattern: Regex pattern that matched
            match: Match object
            full_message: Full error message
            
        Returns:
            Confidence score from 0.0 to 1.0
        """
        base_confidence = 0.7  # Base confidence for any match
        
        # Increase confidence for longer matches
        match_length = len(match.group(0))
        message_length = len(full_message)
        length_bonus = min(0.2, match_length / message_length)
        
        # Increase confidence for patterns with specific keywords
        specific_keywords = [
            'operator', 'function', 'module', 'symbol', 'defined', 
            'redefined', 'missing', 'incorrect', 'level', 'constraint'
        ]
        keyword_bonus = 0.0
        for keyword in specific_keywords:
            if keyword.lower() in pattern.lower():
                keyword_bonus += 0.02
        
        # Decrease confidence for very generic patterns
        generic_penalty = 0.0
        if len(pattern) < 20:  # Very short patterns are less reliable
            generic_penalty = 0.1
        
        final_confidence = min(1.0, base_confidence + length_bonus + keyword_bonus - generic_penalty)
        return final_confidence
    
    def get_error_category(self, error_code: int) -> SANYErrorCategory:
        """Get the category for a SANY error code."""
        if 4000 <= error_code <= 4002:
            return SANYErrorCategory.PARSER_INTERNAL
        elif 4003 <= error_code <= 4005:
            return SANYErrorCategory.INTERNAL_ERROR
        elif 4200 <= error_code <= 4206:
            return SANYErrorCategory.BASIC_SEMANTIC
        elif 4220 <= error_code <= 4224:
            return SANYErrorCategory.MODULE_IMPORT
        elif 4240 <= error_code <= 4247:
            return SANYErrorCategory.INSTANCE_SUBSTITUTION
        elif 4260 <= error_code <= 4262:
            return SANYErrorCategory.FUNCTION_RECORD
        elif 4270 <= error_code <= 4275:
            return SANYErrorCategory.HIGHER_ORDER
        elif 4290 <= error_code <= 4294:
            return SANYErrorCategory.RECURSIVE
        elif 4310 <= error_code <= 4315:
            return SANYErrorCategory.TEMPORAL
        elif 4330 <= error_code <= 4337:
            return SANYErrorCategory.LABEL
        elif 4350 <= error_code <= 4357:  # Updated range to match actual codes
            return SANYErrorCategory.PROOF
        elif error_code >= 9000 and error_code < 9999:  # Custom syntax/parse errors
            return SANYErrorCategory.SYNTAX_PARSE
        elif error_code == 9999:  # Special unknown error code
            return SANYErrorCategory.INTERNAL_ERROR  # Classify unknowns as internal for now
        elif error_code >= 4800:
            return SANYErrorCategory.WARNING
        else:
            return SANYErrorCategory.INTERNAL_ERROR
    
    def get_all_supported_error_codes(self) -> List[int]:
        """Get list of all SANY error codes that can be reverse-engineered."""
        return list(self._error_patterns.keys())
    
    def get_pattern_for_code(self, error_code: int) -> Optional[Tuple[str, str, str]]:
        """Get pattern, name and description for a given error code."""
        return self._error_patterns.get(error_code)


# Convenience functions
def classify_sany_error_message(error_message: str) -> Optional[SANYErrorMatch]:
    """Classify SANY error message using default classifier."""
    classifier = SANYErrorCodeReverse()
    return classifier.classify_sany_error(error_message)


def extract_sany_error_code(error_message: str) -> Optional[int]:
    """Extract SANY error code from error message."""
    match = classify_sany_error_message(error_message)
    return match.error_code if match else None