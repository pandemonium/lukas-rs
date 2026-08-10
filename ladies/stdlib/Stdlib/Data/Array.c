#include "gc.h"

/// Array functions
FOREIGN_DECL(int64_t, Root_Stdlib_Data_Array_Array_raw_len, Value, arr, {
  return (int64_t)tuple_len(arr);
})
FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Array_raw_get, Value, arr, int64_t, index, {
  Tuple *array = as_tuple(arr);
  if (index >= 0 && index < (int64_t)tuple_len(arr)) {
    return perhaps_this(array->elems[index]);
  } else {
    return perhaps_nope();
  }
})


/// Mutable_Array functions
FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Mutable_Array_raw_allocate_mutable_array_uninit, int64_t, size, {
  return mk_tuple_uninit(size);
})

FOREIGN_DECL(int64_t, Root_Stdlib_Data_Array_Mutable_Array_raw_len, Value, arr, {
  return (int64_t)tuple_len(arr);
})

FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Mutable_Array_raw_get, Value, arr, int64_t, index, {
  Tuple *array = as_tuple(arr);
  if (index >= 0 && index < (int64_t)tuple_len(arr)) {
    return perhaps_this(array->elems[index]);
  } else {
    return perhaps_nope();
  }
})

FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Mutable_Array_raw_put, Value, arr, int64_t, index, Value, elt,{
  Tuple *array = as_tuple(arr);
  if (index >= 0 && index < (int64_t)tuple_len(arr)) {
    Value previous = array->elems[index];
    array->elems[index] = elt;
    return perhaps_this(previous);
  } else {
    return perhaps_nope();
  }
})

FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Mutable_Array_raw_get_unchecked, Value, arr, int64_t, index, {
  Tuple *array = as_tuple(arr);
  return array->elems[index];
})

FOREIGN_DECL(Value, Root_Stdlib_Data_Array_Mutable_Array_raw_put_unchecked, Value, arr, int64_t, index, Value, elt, {
  Tuple *array = as_tuple(arr);
  Value previous = array->elems[index];
  array->elems[index] = elt;
  // Does this incur a cost?
  return previous;
})
