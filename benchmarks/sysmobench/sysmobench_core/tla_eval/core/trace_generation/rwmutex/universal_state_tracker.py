"""
Universal RwMutex State Tracker for Multiple TLA+ Specifications

Supports different variable structures through mapping configuration.
Converts incremental system traces to various TLA+ trace validation formats.
"""

import json
from typing import Dict, Any, List


class UniversalRwMutexStateTracker:
    """
    Universal state tracker that can adapt to different TLA+ specification
    variable structures through configuration-driven mapping.
    """

    def __init__(self, threads: List[str] = None, mapping: Dict[str, Any] = None):
        """Initialize universal state tracker with thread configuration and mapping."""
        self.threads = threads or ["Thread0", "Thread1", "Thread2"]
        self.mapping = mapping or {}

        # Track all seen threads dynamically
        self.all_threads = set(self.threads)

        # Initialize internal state (always use flat structure internally)
        self.internal_state = {
            "writer_bit": False,
            "upgradeable_bit": False,
            "being_upgraded_bit": False,
            "reader_count": 0,
            "wait_queue": [],
            "thread_state": {t: "none" for t in self.threads}
        }

        # Load variable structure mapping
        self.variable_structure = self.mapping.get("variable_structure", {})

        # Load action mapping from mapping file
        self.action_mapping = self.mapping.get("action_mappings", {
            "ReadLock": "StartRead",
            "TryReadLock": "StartRead",
            "TryAcquireRead": "StartRead",
            "ReadUnlock": "ReleaseRead",
            "WriteLock": "StartWrite",
            "TryWriteLock": "StartWrite",
            "WriteUnlock": "ReleaseWrite",
        })

    def apply_action(self, trace_step: Dict[str, Any]) -> Dict[str, Any]:
        """
        Apply system trace step and return TLA+ formatted state transition.
        """
        action = trace_step.get("action", "")
        actor_id = trace_step.get("actor", trace_step.get("thread", 0))

        # Convert actor ID to thread name
        actor_thread = self._get_thread_name(actor_id)

        # Apply state changes based on action
        self._update_internal_state(action, actor_thread, trace_step)

        # Generate TLA+ formatted step using variable structure mapping
        return self._generate_tla_step(action)

    def _get_thread_name(self, actor_id) -> str:
        """Convert actor ID to thread name."""
        if isinstance(actor_id, str) and actor_id.startswith("Thread"):
            return actor_id
        return f"Thread{actor_id}"

    def _update_internal_state(self, action: str, actor: str, trace_step: Dict[str, Any]) -> None:
        """Update internal state based on system action."""

        # Add new thread if not seen before
        if actor not in self.all_threads:
            self.all_threads.add(actor)
            self.internal_state["thread_state"][actor] = "none"

        if action in ["ReadLock", "TryReadLock", "TryAcquireRead"]:
            # Acquire read lock
            if not self.internal_state["writer_bit"] and not self.internal_state["being_upgraded_bit"]:
                self.internal_state["reader_count"] += 1
                self.internal_state["thread_state"][actor] = "reading"

        elif action == "ReadUnlock":
            # Release read lock
            if self.internal_state["thread_state"][actor] == "reading":
                self.internal_state["reader_count"] -= 1
                self.internal_state["thread_state"][actor] = "none"

        elif action in ["WriteLock", "TryWriteLock", "TryAcquireWrite"]:
            # Acquire write lock
            if (not self.internal_state["writer_bit"] and
                not self.internal_state["upgradeable_bit"] and
                self.internal_state["reader_count"] == 0 and
                not self.internal_state["being_upgraded_bit"]):

                self.internal_state["writer_bit"] = True
                self.internal_state["thread_state"][actor] = "writing"

        elif action == "WriteUnlock":
            # Release write lock
            if self.internal_state["thread_state"][actor] == "writing":
                self.internal_state["writer_bit"] = False
                self.internal_state["thread_state"][actor] = "none"

        elif action in ["UpreadLock", "TryUpreadLock", "AcquireUpreadSuccess", "TryAcquireUpreadNonBlocking"]:
            # Acquire upgradeable read lock
            if (not self.internal_state["writer_bit"] and
                not self.internal_state["upgradeable_bit"]):

                self.internal_state["upgradeable_bit"] = True
                self.internal_state["thread_state"][actor] = "upgradeable"

        elif action in ["UpreadUnlock", "ReleaseUpread"]:
            # Release upgradeable read lock
            if self.internal_state["thread_state"][actor] == "upgradeable":
                self.internal_state["upgradeable_bit"] = False
                self.internal_state["thread_state"][actor] = "none"

        elif action == "TryUpgradeLock":
            # Start upgrade process
            if (self.internal_state["thread_state"][actor] == "upgradeable" and
                not self.internal_state["being_upgraded_bit"]):

                self.internal_state["being_upgraded_bit"] = True
                self.internal_state["thread_state"][actor] = "upgrading"

        elif action in ["UpgradeLock", "UpgradeUpreadSuccess"]:
            # Complete upgrade to write lock
            if (self.internal_state["thread_state"][actor] == "upgrading" and
                self.internal_state["reader_count"] == 0):

                self.internal_state["writer_bit"] = True
                self.internal_state["being_upgraded_bit"] = False
                self.internal_state["upgradeable_bit"] = False
                self.internal_state["thread_state"][actor] = "writing"

    def _generate_tla_step(self, action: str) -> Dict[str, Any]:
        """Generate TLA+ formatted step based on variable structure mapping."""

        # Map system action to TLA+ event
        tla_event = self.action_mapping.get(action, action)

        step = {"event": tla_event}

        # Generate variables based on structure mapping
        if not self.variable_structure:
            # Fallback to flat structure
            step.update(self._generate_flat_variables())
        else:
            step.update(self._generate_mapped_variables())

        return step

    def _generate_flat_variables(self) -> Dict[str, Any]:
        """Generate flat variable structure (fallback)."""
        return {
            "writer_bit": [{"op": "Update", "path": [], "args": [self.internal_state["writer_bit"]]}],
            "upgradeable_bit": [{"op": "Update", "path": [], "args": [self.internal_state["upgradeable_bit"]]}],
            "being_upgraded_bit": [{"op": "Update", "path": [], "args": [self.internal_state["being_upgraded_bit"]]}],
            "reader_count": [{"op": "Update", "path": [], "args": [self.internal_state["reader_count"]]}],
            "wait_queue": [{"op": "Update", "path": [], "args": [self.internal_state["wait_queue"]]}],
            "thread_state": [{"op": "Update", "path": [], "args": [dict(self.internal_state["thread_state"])]}]
        }

    def _generate_mapped_variables(self) -> Dict[str, Any]:
        """Generate variables based on mapping configuration."""
        result = {}

        variables = self.variable_structure.get("variables", {})

        for var_name, var_config in variables.items():
            var_type = var_config.get("type")

            if var_type == "record":
                # Generate record structure
                record_value = {}
                for field_name, field_config in var_config.get("fields", {}).items():
                    source = field_config.get("source")
                    if source and source in self.internal_state:
                        record_value[field_name] = self.internal_state[source]
                    else:
                        # Use default value based on type
                        field_type = field_config.get("type", "boolean")
                        record_value[field_name] = self._get_default_value(field_type)

                result[var_name] = [{"op": "Update", "path": [], "args": [record_value]}]

            elif var_type == "sequence":
                source = var_config.get("source", "wait_queue")
                seq_value = self.internal_state.get(source, [])
                result[var_name] = [{"op": "Update", "path": [], "args": [seq_value]}]

            elif var_type == "constant":
                const_value = var_config.get("value")
                result[var_name] = [{"op": "Update", "path": [], "args": [const_value]}]

            elif var_type == "function":
                source = var_config.get("source", "thread_state")
                mapping = var_config.get("mapping", {})

                if source in self.internal_state:
                    func_value = {}
                    for thread, state in self.internal_state[source].items():
                        mapped_state = mapping.get(state, state)
                        func_value[thread] = mapped_state
                    result[var_name] = [{"op": "Update", "path": [], "args": [func_value]}]

            elif var_type == "nat":
                # For GPT5's bit-encoded lock
                if var_config.get("encoding") == "bitfield":
                    # Simplified bit encoding (would need full implementation for GPT5)
                    lock_value = self.internal_state["reader_count"]
                    if self.internal_state["being_upgraded_bit"]:
                        lock_value += 2**28  # BG bit
                    if self.internal_state["upgradeable_bit"]:
                        lock_value += 2**29  # UR bit
                    if self.internal_state["writer_bit"]:
                        lock_value += 2**30  # WR bit
                    result[var_name] = [{"op": "Update", "path": [], "args": [lock_value]}]

        return result

    def _get_default_value(self, type_name: str):
        """Get default value for a type."""
        defaults = {
            "boolean": False,
            "nat": 0,
            "string": "",
            "sequence": []
        }
        return defaults.get(type_name, None)

    def get_initial_config(self) -> Dict[str, Any]:
        """Get initial configuration line for TLA+ trace."""
        return {"Threads": sorted(list(self.all_threads))}