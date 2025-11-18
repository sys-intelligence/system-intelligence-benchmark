# Import anything you need below

# Put tunable constant parameters below
ALPHA = 0.0

# Put the metadata specifically maintained by the policy below.
m_key_timestamp = dict()


def evict(cache_snapshot, obj):
    candid_obj_key = None
    min_ts = min(m_key_timestamp.values())
    candid_obj_keys = list(key for key in cache_snapshot.cache if m_key_timestamp[key] == min_ts)
    candid_obj_key = candid_obj_keys[0]
    return candid_obj_key


def update_after_hit(cache_snapshot, obj):
    assert obj.key in m_key_timestamp


def update_after_insert(cache_snapshot, obj):
    global m_key_timestamp
    assert obj.key not in m_key_timestamp
    m_key_timestamp[obj.key] = cache_snapshot.access_count


def update_after_evict(cache_snapshot, obj, evicted_obj):
    global m_key_timestamp
    assert obj.key not in m_key_timestamp
    assert evicted_obj.key in m_key_timestamp
    m_key_timestamp.pop(evicted_obj.key)
