#include "gc.h"

FOREIGN_DECL(int64_t, Root_Stdlib_Array_raw_len, Value, arr, {
  return as_tuple(arr)->len;
})

FOREIGN_DECL(Value, Root_Stdlib_Array_raw_get_element, Value, arr, int64_t, index, {
  Tuple *array = as_tuple(arr);
  if (index >= 0 && index < array->len) {
    return perhaps_this(array->elems[index]);
  } else {
    return perhaps_nope();
  }
})
