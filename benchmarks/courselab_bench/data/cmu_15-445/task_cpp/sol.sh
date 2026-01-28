#!/bin/bash
set -e

# Reference solution for CMU 15-445 CountMinSketch task

cat > src/primer/count_min_sketch.cpp << 'EOF'
//===----------------------------------------------------------------------===//
//
//                         BusTub
//
// count_min_sketch.cpp
//
// Identification: src/primer/count_min_sketch.cpp
//
// Copyright (c) 2015-2025, Carnegie Mellon University Database Group
//
//===----------------------------------------------------------------------===//

#include "primer/count_min_sketch.h"

#include <algorithm>
#include <stdexcept>
#include <string>

namespace bustub {

/**
 * Constructor for the count-min sketch.
 *
 * @param width The width of the sketch matrix.
 * @param depth The depth of the sketch matrix.
 * @throws std::invalid_argument if width or depth are zero.
 */
template <typename KeyType>
CountMinSketch<KeyType>::CountMinSketch(uint32_t width, uint32_t depth) : width_(width), depth_(depth) {
  if (width == 0 || depth == 0) {
    throw std::invalid_argument("Width and depth must be greater than zero");
  }

  // Initialize the sketch matrix with zeros using a flat array
  size_t total_size = static_cast<size_t>(depth_) * width_;
  sketch_ = std::make_unique<std::atomic<uint32_t>[]>(total_size);
  for (size_t i = 0; i < total_size; i++) {
    sketch_[i].store(0, std::memory_order_relaxed);
  }

  /** @spring2026 PLEASE DO NOT MODIFY THE FOLLOWING */
  // Initialize seeded hash functions
  hash_functions_.reserve(depth_);
  for (size_t i = 0; i < depth_; i++) {
    hash_functions_.push_back(this->HashFunction(i));
  }
}

template <typename KeyType>
CountMinSketch<KeyType>::CountMinSketch(CountMinSketch &&other) noexcept
    : width_(other.width_),
      depth_(other.depth_),
      sketch_(std::move(other.sketch_)) {

  // Reinitialize hash functions with the new object's 'this' pointer
  hash_functions_.reserve(depth_);
  for (size_t i = 0; i < depth_; i++) {
    hash_functions_.push_back(this->HashFunction(i));
  }

  // Reset the other object to a valid but empty state
  other.width_ = 0;
  other.depth_ = 0;
  other.hash_functions_.clear();
}

template <typename KeyType>
auto CountMinSketch<KeyType>::operator=(CountMinSketch &&other) noexcept -> CountMinSketch & {
  if (this != &other) {
    width_ = other.width_;
    depth_ = other.depth_;
    sketch_ = std::move(other.sketch_);

    // Reinitialize hash functions with the new object's 'this' pointer
    hash_functions_.clear();
    hash_functions_.reserve(depth_);
    for (size_t i = 0; i < depth_; i++) {
      hash_functions_.push_back(this->HashFunction(i));
    }

    // Reset the other object to a valid but empty state
    other.width_ = 0;
    other.depth_ = 0;
    other.hash_functions_.clear();
  }
  return *this;
}

template <typename KeyType>
void CountMinSketch<KeyType>::Insert(const KeyType &item) {
  // For each hash function (row), compute the hash and increment the corresponding cell
  for (uint32_t i = 0; i < depth_; i++) {
    size_t col = hash_functions_[i](item);
    size_t idx = GetIndex(i, col);
    // Use fetch_add for thread-safe atomic increment
    sketch_[idx].fetch_add(1, std::memory_order_relaxed);
  }
}

template <typename KeyType>
void CountMinSketch<KeyType>::Merge(const CountMinSketch<KeyType> &other) {
  if (width_ != other.width_ || depth_ != other.depth_) {
    throw std::invalid_argument("Incompatible CountMinSketch dimensions for merge.");
  }

  // Add each cell from the other sketch to this one
  size_t total_size = static_cast<size_t>(depth_) * width_;
  for (size_t i = 0; i < total_size; i++) {
    uint32_t other_val = other.sketch_[i].load(std::memory_order_relaxed);
    sketch_[i].fetch_add(other_val, std::memory_order_relaxed);
  }
}

template <typename KeyType>
auto CountMinSketch<KeyType>::Count(const KeyType &item) const -> uint32_t {
  if (depth_ == 0 || width_ == 0 || !sketch_) {
    return 0;
  }

  // Get the minimum count across all hash functions
  uint32_t min_count = UINT32_MAX;
  for (uint32_t i = 0; i < depth_; i++) {
    size_t col = hash_functions_[i](item);
    size_t idx = GetIndex(i, col);
    uint32_t count = sketch_[idx].load(std::memory_order_relaxed);
    min_count = std::min(min_count, count);
  }

  return min_count;
}

template <typename KeyType>
void CountMinSketch<KeyType>::Clear() {
  // Reset all counters to zero
  if (sketch_) {
    size_t total_size = static_cast<size_t>(depth_) * width_;
    for (size_t i = 0; i < total_size; i++) {
      sketch_[i].store(0, std::memory_order_relaxed);
    }
  }
}

template <typename KeyType>
auto CountMinSketch<KeyType>::TopK(uint16_t k, const std::vector<KeyType> &candidates)
    -> std::vector<std::pair<KeyType, uint32_t>> {
  // Get counts for all candidates
  std::vector<std::pair<KeyType, uint32_t>> items_with_counts;
  items_with_counts.reserve(candidates.size());

  for (const auto &candidate : candidates) {
    uint32_t count = Count(candidate);
    items_with_counts.emplace_back(candidate, count);
  }

  // Sort by count in descending order
  std::sort(items_with_counts.begin(), items_with_counts.end(),
            [](const auto &a, const auto &b) {
              return a.second > b.second;
            });

  // Return top k items (or all if fewer than k)
  size_t result_size = std::min(static_cast<size_t>(k), items_with_counts.size());
  return std::vector<std::pair<KeyType, uint32_t>>(
      items_with_counts.begin(),
      items_with_counts.begin() + result_size);
}

// Explicit instantiations for all types used in tests
template class CountMinSketch<std::string>;
template class CountMinSketch<int64_t>;  // For int64_t tests
template class CountMinSketch<int>;      // This covers both int and int32_t
}  // namespace bustub
EOF

cat > src/include/primer/count_min_sketch.h << 'EOF'
//===----------------------------------------------------------------------===//
//
//                         BusTub
//
// count_min_sketch.h
//
// Identification: src/include/primer/count_min_sketch.h
//
// Copyright (c) 2015-2025, Carnegie Mellon University Database Group
//
//===----------------------------------------------------------------------===//

#pragma once

#include <atomic>
#include <cstdint>
#include <functional>
#include <memory>
#include <utility>
#include <vector>

#include "common/util/hash_util.h"

namespace bustub {

template <typename KeyType>
class CountMinSketch {
 public:
  /** @brief Constructs a count-min sketch with specified dimensions
   * @param width Number of buckets
   * @param depth Number of hash functions
   */
  explicit CountMinSketch(uint32_t width, uint32_t depth);

  CountMinSketch() = delete;                                            // Default constructor deleted
  CountMinSketch(const CountMinSketch &) = delete;                      // Copy constructor deleted
  auto operator=(const CountMinSketch &) -> CountMinSketch & = delete;  // Copy assignment deleted

  CountMinSketch(CountMinSketch &&other) noexcept;                      // Move constructor
  auto operator=(CountMinSketch &&other) noexcept -> CountMinSketch &;  // Move assignment

  /**
   * @brief Inserts an item into the count-min sketch
   *
   * @param item The item to increment the count for
   * @note Updates the min-heap at the same time
   */
  void Insert(const KeyType &item);

  /**
   * @brief Gets the estimated count of an item
   *
   * @param item The item to look up
   * @return The estimated count
   */
  auto Count(const KeyType &item) const -> uint32_t;

  /**
   * @brief Resets the sketch to initial empty state
   *
   * @note Clears the sketch matrix, item set, and top-k min-heap
   */
  void Clear();

  /**
   * @brief Merges the current CountMinSketch with another, updating the current sketch
   * with combined data from both sketches.
   *
   * @param other The other CountMinSketch to merge with.
   * @throws std::invalid_argument if the sketches' dimensions are incompatible.
   */
  void Merge(const CountMinSketch<KeyType> &other);

  /**
   * @brief Gets the top k items based on estimated counts from a list of candidates.
   *
   * @param k Number of top items to return (will be capped at initial k)
   * @param candidates List of candidate items to consider for top k
   * @return Vector of (item, count) pairs in descending count order
   */
  auto TopK(uint16_t k, const std::vector<KeyType> &candidates) -> std::vector<std::pair<KeyType, uint32_t>>;

 private:
  /** Dimensions of the count-min sketch matrix */
  uint32_t width_;  // Number of buckets for each hash function
  uint32_t depth_;  // Number of independent hash functions
  /** Pre-computed hash functions for each row */
  std::vector<std::function<size_t(const KeyType &)>> hash_functions_;

  /** The sketch matrix - using unique_ptr to array of atomics to avoid move/copy issues */
  std::unique_ptr<std::atomic<uint32_t>[]> sketch_;

  /** @spring2026 PLEASE DO NOT MODIFY THE FOLLOWING */
  constexpr static size_t SEED_BASE = 15445;

  /**
   * @brief Seeded hash function generator
   *
   * @param seed Used for creating independent hash functions
   * @return A function that maps items to column indices
   */
  inline auto HashFunction(size_t seed) -> std::function<size_t(const KeyType &)> {
    return [seed, this](const KeyType &item) -> size_t {
      auto h1 = std::hash<KeyType>{}(item);
      auto h2 = bustub::HashUtil::CombineHashes(seed, SEED_BASE);
      return bustub::HashUtil::CombineHashes(h1, h2) % width_;
    };
  }

  /** Helper function to get the index in the flat array */
  inline auto GetIndex(uint32_t row, uint32_t col) const -> size_t {
    return static_cast<size_t>(row) * width_ + col;
  }

  /** @todo (student) can add their data structures that support count-min sketch operations */
};

}  // namespace bustub
EOF
