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
FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Mutable_Array_raw_generate, int64_t, length, Value, mk_element, {
  return flat_generate(length, mk_element);
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

FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Mutable_Array_raw_put_unchecked, Value, arr, int64_t, index, Value, elt, {
  return flat_array_put(arr, (size_t)index, elt);
})
