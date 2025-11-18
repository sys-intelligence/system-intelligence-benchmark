# Import anything you need below
import collections
import logging

# Put tunable constant parameters below
LEARNING_RATE = 0.1

# Put the metadata specifically maintained by the policy below. The policy maintains a predictive heuristic score, a temporal decay value, and a dynamic learning matrix for each cache entry. The heuristic score predicts future access patterns, the temporal decay value tracks the recency of access, and the dynamic learning matrix adjusts based on access patterns over time.
heuristic_scores = {}
insertion_times = {}
dynamic_learning_matrix = collections.defaultdict(lambda: collections.defaultdict(float))


def evict(cache_snapshot, obj):
    """This function defines how the policy chooses the eviction victim.
    The policy chooses the eviction victim by combining the predictive heuristic score and the temporal decay value. Entries with the lowest combined score are selected for eviction, ensuring that both recent and predicted future accesses are considered.
    - Args:
        - `cache_snapshot`: A snapshot of the current cache state.
        - `obj`: The new object that needs to be inserted into the cache.
    - Return:
        - `candid_obj_key`: The key of the cached object that will be evicted to make room for `obj`.
    """
    sorted_keys = sorted(cache_snapshot.cache.keys(), key=lambda key: (heuristic_scores[key], insertion_times[key]))
    if len(sorted_keys) > 1:
        if (
            heuristic_scores[sorted_keys[0]] == heuristic_scores[sorted_keys[1]]
            and insertion_times[sorted_keys[0]] >= insertion_times[sorted_keys[1]]
        ):
            logging.fatal(
                f'ERROR: ({sorted_keys[0]}: {heuristic_scores[sorted_keys[0]]}, {insertion_times[sorted_keys[0]]}) ({sorted_keys[1]}: {heuristic_scores[sorted_keys[1]]}, {insertion_times[sorted_keys[1]]})'
            )

    # print(sorted_keys[0])
    return sorted_keys[0]


def update_after_hit(cache_snapshot, obj):
    """This function defines how the policy update the metadata it maintains immediately after a cache hit.
    Upon a cache hit, the predictive heuristic score is updated based on the dynamic learning matrix, which adjusts according to the observed access pattern. The temporal decay value is reset to reflect the recent access.
    - Args:
        - `cache_snapshot`: A snapshot of the current cache state.
        - `obj`: The object accessed during the cache hit.
    - Return: `None`
    """
    key = obj.key
    for other_key in cache_snapshot.cache:
        if other_key != key:
            dynamic_learning_matrix[key][other_key] += LEARNING_RATE

    # print(dynamic_learning_matrix)


def update_after_insert(cache_snapshot, obj):
    """This function defines how the policy updates the metadata it maintains immediately after inserting a new object into the cache.
    After inserting a new object, the policy initializes the predictive heuristic score using the dynamic learning matrix and sets the temporal decay value to its initial state. The dynamic learning matrix is updated to incorporate the new access pattern.
    - Args:
        - `cache_snapshot`: A snapshot of the current cache state.
        - `obj`: The object that was just inserted into the cache.
    - Return: `None`
    """
    key = obj.key
    heuristic_scores[key] = sum(dynamic_learning_matrix[key].values())
    insertion_times[key] = cache_snapshot.access_count
    for other_key in cache_snapshot.cache:
        dynamic_learning_matrix[key][other_key] += LEARNING_RATE

    # print(dynamic_learning_matrix)


def update_after_evict(cache_snapshot, obj, evicted_obj):
    """This function defines how the policy updates the metadata it maintains immediately after evicting the victim.
    Following an eviction, the policy updates the dynamic learning matrix to reduce the weight of the evicted entry's access pattern, ensuring that the matrix adapts to the changing cache contents and access patterns.
    - Args:
        - `cache_snapshot`: A snapshot of the current cache state.
        - `obj`: The object to be inserted into the cache.
        - `evicted_obj`: The object that was just evicted from the cache.
    - Return: `None`
    """
    evicted_key = evicted_obj.key
    for key in dynamic_learning_matrix:
        if evicted_key in dynamic_learning_matrix[key]:
            dynamic_learning_matrix[key][evicted_key] *= 1 - LEARNING_RATE
    if evicted_key in heuristic_scores:
        del heuristic_scores[evicted_key]

    # print(dynamic_learning_matrix)
