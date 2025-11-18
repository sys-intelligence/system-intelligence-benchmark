# Import anything you need below
from collections import OrderedDict

# Put tunable constant parameters below
PROTECTED_RATIO = 0.8  # Fraction of the cache allocated to the protected segment

# Put the metadata specifically maintained by the policy below.
# Two OrderedDicts to represent the probation and protected segments
probation_segment = OrderedDict()  # Stores newly inserted objects
protected_segment = OrderedDict()  # Stores frequently accessed objects

def evict(cache_snapshot, obj):
    '''
    This function defines how the policy chooses the eviction victim.
    - Args:
        - `cache_snapshot`: A snapshot of the current cache state.
        - `obj`: The new object that needs to be inserted into the cache.
    - Return:
        - `candid_obj_key`: The key of the cached object that will be evicted to make room for `obj`.
    '''
    candid_obj_key = None
    # Your code below
    # Determine the maximum size of the protected segment
    protected_capacity = int(cache_snapshot.capacity * PROTECTED_RATIO)

    # Evict from the probation segment if it has objects
    if len(probation_segment) > 0:
        candid_obj_key = next(iter(probation_segment))
    # Otherwise, evict from the protected segment
    elif len(protected_segment) > 0:
        candid_obj_key = next(iter(protected_segment))

    return candid_obj_key

def update_after_hit(cache_snapshot, obj):
    '''
    This function defines how the policy update the metadata it maintains immediately after a cache hit.
    - Args:
        - `cache_snapshot`: A snapshot of the current cache state.
        - `obj`: The object accessed during the cache hit.
    - Return: `None`
    '''
    # Your code below
    # If the object is in the probation segment, move it to the protected segment
    if obj.key in probation_segment:
        probation_segment.pop(obj.key)
        protected_segment[obj.key] = cache_snapshot.access_count
    # If the object is in the protected segment, update its recency
    elif obj.key in protected_segment:
        protected_segment.move_to_end(obj.key)

def update_after_insert(cache_snapshot, obj):
    '''
    This function defines how the policy updates the metadata it maintains immediately after inserting a new object into the cache.
    - Args:
        - `cache_snapshot`: A snapshot of the current cache state.
        - `obj`: The object that was just inserted into the cache.
    - Return: `None`
    '''
    # Your code below
    # Add the new object to the probation segment
    probation_segment[obj.key] = cache_snapshot.access_count

def update_after_evict(cache_snapshot, obj, evicted_obj):
    '''
    This function defines how the policy updates the metadata it maintains immediately after evicting the victim.
    - Args:
        - `cache_snapshot`: A snapshot of the current cache state.
        - `obj`: The object to be inserted into the cache.
        - `evicted_obj`: The object that was just evicted from the cache.
    - Return: `None`
    '''
    # Your code below
    # Remove the evicted object from the appropriate segment
    if evicted_obj.key in probation_segment:
        del probation_segment[evicted_obj.key]
    elif evicted_obj.key in protected_segment:
        del protected_segment[evicted_obj.key]