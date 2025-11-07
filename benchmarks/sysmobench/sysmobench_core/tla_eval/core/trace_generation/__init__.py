"""
Trace Generation Module

This module handles the generation of runtime traces from distributed systems.
Currently supports etcd raft clusters with plans for additional systems.
"""

from .etcd.cluster import RaftCluster, FileTraceLogger
from .etcd.event_driver import RandomEventDriver

__all__ = ['RaftCluster', 'FileTraceLogger', 'RandomEventDriver']