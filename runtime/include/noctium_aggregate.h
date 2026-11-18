#ifndef NOCTIUM_AGGREGATE_H
#define NOCTIUM_AGGREGATE_H
#include <stddef.h>
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif
#define NOCTIUM_AGGREGATE_ABI_VERSION 1u
#define NOCTIUM_AGGREGATE_MAX_BYTES 1048576u
#define NOCTIUM_AGGREGATE_MAX_BUFFERS 64u
/* ABI version 1. Status codes match noctium_runtime.h. Inputs are borrowed
 * UTF-8 schema/value JSON or canonical aggregate wire bytes. Output tokens use
 * a separate namespace and each successful allocation requires buffer_free.
 * Tokens are process-local ownership IDs, not security capabilities.
 * Returned bytes contain caller values. Do not log or publish private values.
 * Every output scalar clears before validation. No partial copies occur.
 * Non-null pointers require readable/writable, aligned, nonoverlapping storage.
 * Panic containment excludes invalid pointers, aborts and allocator exhaustion.
 * Calls are thread safe. Free is synchronized with copy. Buffer release wipes
 * retained bytes best effort. Temporary parser, arithmetic and encoding copies
 * have no complete zeroization guarantee. Caller copies remain the caller's
 * responsibility. No callbacks or I/O occur in this library. */
uint32_t noctium_aggregate_abi_version(void);
int32_t noctium_aggregate_encode(const uint8_t *schema, size_t schema_length,
                                  const uint8_t *value, size_t value_length,
                                  uint64_t *out_buffer);
int32_t noctium_aggregate_decode(const uint8_t *schema, size_t schema_length,
                                  const uint8_t *wire, size_t wire_length,
                                  uint64_t *out_buffer);
int32_t noctium_aggregate_buffer_length(uint64_t token, size_t *out_length);
int32_t noctium_aggregate_buffer_copy(uint64_t token, uint8_t *destination,
                                       size_t capacity, size_t *out_written);
int32_t noctium_aggregate_buffer_free(uint64_t token);
#ifdef __cplusplus
}
#endif
#endif
