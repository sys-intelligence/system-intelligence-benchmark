"""Trim utility for langchain message types."""

import copy
from langchain_core.messages import HumanMessage


def trim_messages_conservative(
    messages,
    kept_threshold: int = 30
):
    """
    Trim messages by keeping the last kept_threshold messages unchanged,
    and replacing HumanMessage content with "..." for earlier messages.
    
    Args:
        messages: List of langchain messages to trim
        kept_threshold: Number of messages to keep unchanged from the end (default: 30)
        
    Returns:
        Deep copy of trimmed messages without modifying the original
    """
    # Create a deep copy to avoid modifying the original
    trimmed_messages = copy.deepcopy(messages)
    
    trim_sum = 0
    # If we have fewer messages than the threshold, return all unchanged
    if len(trimmed_messages) <= kept_threshold:
        return trimmed_messages, 0
    
    # Calculate how many messages to process from the beginning
    messages_to_trim = len(trimmed_messages) - kept_threshold
    
    # Process the first messages_to_trim messages
    for i in range(messages_to_trim):
        message = trimmed_messages[i]
        # Only replace content for HumanMessage, keep others unchanged
        if isinstance(message, HumanMessage):
            message.content = "..."
            trim_sum += 1
    return trimmed_messages, trim_sum 
