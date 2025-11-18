import os
import sys

sys.path.append(os.path.dirname(os.path.abspath(__file__)))
import random

random.seed(42)  # set the random seed before importing `My` to enable reproduction
import importlib

import My


class CacheObj:
    def __init__(self, key, size, consider_obj_size):
        if not isinstance(key, str):
            raise ValueError('KEY must be a string.')
        if not isinstance(size, int) or not size > 0:
            raise ValueError('SIZE must be a positive integer.')

        self.__key = key
        self.__size = size if consider_obj_size else 1  # size in bytes

    @property
    def size(self):  # read-only
        return self.__size

    @property
    def key(self):  # read-only
        return self.__key


class CacheConfig:
    def __init__(
        self, capacity: int, consider_obj_size: bool, trace_path, key_col_id, size_col_id, has_header: bool, delimiter
    ):
        if not isinstance(capacity, int) or not capacity > 0:
            raise ValueError('CAPACITY must be a positive integer.')

        if not isinstance(consider_obj_size, bool):
            raise ValueError('CONSIDER_OBJ_SIZE msut be a boolean value.')

        if not os.path.exists(trace_path):
            raise ValueError('TRACE_PATH must be an existing path.')

        self.capacity = capacity
        self.consider_obj_size = consider_obj_size
        # parameters for trace
        self.trace_path = trace_path
        self.key_col_id = key_col_id
        self.size_col_id = size_col_id
        self.has_header = has_header
        self.delimiter = delimiter

    def to_dict(self) -> dict:
        return {
            'capacity': self.capacity,
            'consider_obj_size': self.consider_obj_size,
            'trace_path': self.trace_path,
            'key_col_id': self.key_col_id,
            'size_col_id': self.size_col_id,
            'has_header': self.has_header,
            'delimiter': self.delimiter,
        }


class Cache:
    def __init__(self, config: CacheConfig):
        assert isinstance(config, CacheConfig)

        self.__capacity = config.capacity
        self.__cache = dict()  # a map from key to cache_obj
        self.__naccess = 0
        self.__nhit = 0
        importlib.reload(My)
        self.update_after_insert_func = My.update_after_insert
        self.update_after_evict_func = My.update_after_evict
        self.update_after_hit_func = My.update_after_hit
        self.evict_func = My.evict

    @property
    def cache(self):  # read-only
        return self.__cache

    @property
    def size(self):  # read-only
        tot_size = 0
        for obj in self.__cache.values():
            assert isinstance(obj, CacheObj)
            obj_size = obj.size
            assert isinstance(obj_size, int) and obj_size > 0
            tot_size += obj_size
        return tot_size

    @property
    def capacity(self):  # read-only
        return self.__capacity

    @property
    def access_count(self):
        return self.__naccess

    @property
    def hit_count(self):
        return self.__nhit

    @property
    def miss_count(self):
        return self.__naccess - self.__nhit

    @property
    def snapshot(self):  # read-only
        return self

    def get(self, obj) -> bool:  # never exposed to LLM
        self.__naccess += 1

        if not isinstance(obj, CacheObj):
            raise ValueError('OBJ must be an instance of CacheObj')

        if obj.key in self.cache:
            # hit, return true
            # update
            self.__nhit += 1
            self.update_after_hit(obj)
            return True
        else:
            # miss, return False
            if not self.can_insert(obj):
                return False
            if not self.admit(obj):
                return False
            while self.size + obj.size > self.capacity:
                evicted_cache_object = self.evict(obj)
                self.update_after_evict(obj, evicted_cache_object)
            assert self.size + obj.size <= self.capacity
            self.insert(obj)
            self.update_after_insert(obj)
            return False

    def update_after_hit(self, obj):  # never exposed to LLM
        if not isinstance(obj, CacheObj):
            raise ValueError('OBJ must be an instance of CacheObj.')
        if obj.key not in self.__cache:
            raise ValueError('OBJ must be in cache after hit.')

        self.update_after_hit_func(self.snapshot, obj)

    def update_after_insert(self, obj):  # never exposed to LLM
        if not isinstance(obj, CacheObj):
            raise ValueError('OBJ must be an instance of CacheObj.')
        if obj.key not in self.__cache:
            raise ValueError('OBJ must be in cache after insert.')

        self.update_after_insert_func(self.snapshot, obj)

    def update_after_evict(self, obj, evicted_obj):  # never exposed to LLM
        if not isinstance(obj, CacheObj):
            raise ValueError('OBJ must be an instance of CacheObj.')
        if obj.key in self.__cache:
            raise ValueError('OBJ must not be in cache before eviction completes.')
        if evicted_obj != None:
            if not isinstance(evicted_obj, CacheObj):
                raise ValueError('EVICTED_OBJ must be an instance of CacheObj if not None.')
            if evicted_obj.key in self.__cache:
                raise ValueError('EVICTED_OBJ must not be in cache after eviction.')
        else:
            raise ValueError('EVICTIED_OBJ must not be None.')

        self.update_after_evict_func(self.snapshot, obj, evicted_obj)

    def evict(self, obj):  # never exposed to LLM
        """Return:
        - evicted_cache_obj (CacheObj): the evicted cache object.
        """
        candid_obj_key = self.evict_func(self.snapshot, obj)
        if candid_obj_key == None or candid_obj_key not in self.__cache:
            raise ValueError('CANDID_OBJ_KEY must be in cache')
        assert candid_obj_key != None
        assert candid_obj_key in self.__cache
        candid_obj_size = self.__cache[candid_obj_key].size
        old_size = self.size
        evicted_cache_obj = self.__cache.pop(candid_obj_key)
        new_size = self.size
        assert new_size == old_size - candid_obj_size
        return evicted_cache_obj

    def insert(self, obj):  # never exposed to LLM
        assert obj.key not in self.__cache
        old_size = self.size
        obj_size = obj.size
        self.__cache[obj.key] = obj
        new_size = self.size
        assert old_size + obj_size == new_size

    def can_insert(self, obj):  # never exposed to LLM
        if obj.size > self.capacity:
            return False
        return True

    def admit(self, obj):  # never exposed to LLM
        should_admit = self.capacity >= obj.size
        assert isinstance(should_admit, bool)
        return should_admit
