#include "gc.h"

/// Array functions
///
/// A readonly `Array` is built flat too (by `mk_flat_array_from` for a `[...]`
/// literal -- the only source), so access strides the same flat backing as
/// `Mutable_Array`: `raw_get` boxes the element back out to canonical form.
FOREIGN_DECL(int64_t, Root_Stdlib_Data_Array_Array_raw_len, Value, arr, {
  return (int64_t)flat_array_count(arr);
})
FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Array_raw_get, Value, arr, int64_t, index, {
  if (index >= 0 && index < (int64_t)flat_array_count(arr)) {
    return perhaps_this(flat_array_get(arr, (size_t)index));
  } else {
    return perhaps_nope();
  }
})


/// Mutable_Array functions
///
/// Backed by the flat-array runtime (gc.c): one heap object holds all elements
/// inline. A product element (tuple/record) is stored flattened -- so an array
/// of N records is ONE GC object, not N+1; an Int/sum/text element keeps the
/// one-word-per-slot layout. `raw_generate` builds the whole array in C,
/// discovering the element width from element 0; get/put box out / copy in the
/// flat<->canonical coercion so every caller only ever sees canonical values.
// The `Memory_Layout α` constraint threads its dictionary in as the leading value
// argument: a one-field record `{ shape }` whose `shape` (field 0) is a `Raw_Shape`
// -- a byte body holding `[slen, shape...]`. Packing each element by that type-driven
// shape lets a sum element store inline (element-0 discovery could not see the other
// variants). `dict` is a live root on the stack across `flat_generate_shaped`.
FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Mutable_Array_raw_generate_shaped, Value, dict, int64_t, length, Value, mk_element, {
  int64_t *entries = (int64_t *)as_ptr(proj(dict, 0));
  size_t slen = (size_t)entries[0];
  // A shape with no sum node needs no type-directed packing. Concrete record
  // codegen may already have flattened its value, so recursively applying the
  // record shape here would flatten it twice. Element-0 discovery handles these
  // scalar/product layouts and agrees with their emitted representation.
  bool has_sum = false;
  for (size_t i = 1; i <= slen; i++) has_sum |= entries[i] < 0;
  if (!has_sum) return flat_generate(length, mk_element);
  return flat_generate_shaped(length, mk_element, entries + 1, slen);
})

FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Mutable_Array_raw_from_enumerator_shaped, Value, dict, int64_t, length, Value, enumeration, Value, next, {
  int64_t *entries = (int64_t *)as_ptr(proj(dict, 0));
  size_t slen = (size_t)entries[0];
  bool has_sum = false;
  for (size_t i = 1; i <= slen; i++) has_sum |= entries[i] < 0;
  if (!has_sum)
    return flat_from_enumerator(length, enumeration, next);
  return flat_from_enumerator_shaped(length, enumeration, next,
                                     entries + 1, slen);
})

FOREIGN_DECL(int64_t, Root_Stdlib_Data_Array_Mutable_Array_raw_len, Value, arr, {
  return (int64_t)flat_array_count(arr);
})

FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Mutable_Array_raw_get, Value, arr, int64_t, index, {
  if (index >= 0 && index < (int64_t)flat_array_count(arr)) {
    return perhaps_this(flat_array_get(arr, (size_t)index));
  } else {
    return perhaps_nope();
  }
})

FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Mutable_Array_raw_put, Value, arr, int64_t, index, Value, elt,{
  if (index >= 0 && index < (int64_t)flat_array_count(arr)) {
    return perhaps_this(flat_array_put(arr, (size_t)index, elt));
  } else {
    return perhaps_nope();
  }
})

FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Mutable_Array_raw_get_unchecked, Value, arr, int64_t, index, {
  return flat_array_get(arr, (size_t)index);
})

FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Mutable_Array_raw_get_niche_payload_unchecked, Value, arr, int64_t, index, {
  return flat_array_get_niche_payload_unchecked(arr, (size_t)index);
})

FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Mutable_Array_raw_put_unchecked, Value, arr, int64_t, index, Value, elt, {
  return flat_array_put(arr, (size_t)index, elt);
})

// Write-only counterpart to `raw_put_unchecked`: copy the new canonical value
// into the packed slot without first rebuilding and returning the old element.
FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Mutable_Array_raw_set_unchecked, Value, arr, int64_t, index, Value, elt, {
  flat_array_set(arr, (size_t)index, elt);
  return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Mutable_Array_raw_copy_unchecked,
             Value, source, int64_t, source_index,
             Value, target, int64_t, target_index, int64_t, count, {
  flat_array_copy(source, (size_t)source_index,
                  target, (size_t)target_index, (size_t)count);
  return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Mutable_Array_raw_grow_with,
             Value, source, int64_t, new_length, Value, fill, {
  if (new_length < 0) match_fail();
  return flat_array_grow_with(source, (size_t)new_length, fill);
})
