###
# Import anything you need here
###

###
# Tunable constant parameters here
###

###
# Additional variables here
###
m_key_frequency = dict()
m_key_ts = dict()


def evict(cache_snapshot, obj):
    candid_obj_key = None
    candid_obj_key = min(m_key_frequency.keys(), key=lambda k: (m_key_frequency[k], m_key_ts[k]))
    return candid_obj_key


def update_after_hit(cache_snapshot, obj):
    assert obj.key in m_key_frequency
    assert obj.key in m_key_ts
    m_key_frequency[obj.key] += 1
    m_key_ts[obj.key] = cache_snapshot.access_count


def update_after_insert(cache_snapshot, obj):
    assert obj.key not in m_key_frequency
    assert obj.key not in m_key_ts
    m_key_frequency[obj.key] = 1
    m_key_ts[obj.key] = cache_snapshot.access_count


def update_after_evict(cache_snapshot, obj, evicted_obj):
    assert obj.key not in m_key_frequency
    assert obj.key not in m_key_ts
    assert evicted_obj.key in m_key_frequency
    assert evicted_obj.key in m_key_ts
    m_key_frequency.pop(evicted_obj.key)
    m_key_ts.pop(evicted_obj.key)
