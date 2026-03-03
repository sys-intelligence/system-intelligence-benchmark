"""System Intelligence SDK package."""

from importlib.metadata import PackageNotFoundError, version

try:
    __version__ = version('system-intelligence-sdk')
except PackageNotFoundError:
    __version__ = '0.0.0'

__all__ = ['__version__']
