// C implementation of the private `foreign` primitives in Root.lady's Files
// module. The Marmelade `FILE` type is opaque; here it is a real FILE* smuggled
// through the boxed Value as an Int. These names are private to Files on the
// Marmelade side -- only Files's own (safe) surface can reach them.
#include "gc.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <errno.h>

// prim_open : Text -> Text -> FILE   (path, mode)
// Text is an OBJ_SLICE (length-prefixed, no NUL) -> copy each into a NUL-terminated buffer.
FOREIGN_DECL(int64_t, Root_Files_prim_open, Value, path, Value, mode, {
    char p[4096];
    char m[16];
    if (!text_to_cstr(path, p, sizeof p) || !text_to_cstr(mode, m, sizeof m))
        return (int64_t)(intptr_t)NULL;
    return (int64_t)(intptr_t)fopen(p, m);
})

// prim_write_line : FILE -> Text -> Unit  (write the slice's bytes; no NUL needed)
FOREIGN_DECL(Value, Root_Files_prim_write_line, int64_t, h, Value, line, {
    FILE *f = (FILE *)(intptr_t)h;
    fwrite(slice_ptr(line), 1, slice_len(line), f);
    fputc('\n', f);
    return VUnit();
})

// prim_read_line : FILE -> Text   (newline stripped)
// Returns a *borrowed* pointer; OF_Text copies it into a collectable heap text,
// so there is nothing to malloc or free. Thebuffer is `static` (not a plain
// local) because the macro copies it *after* this body returns -- a stack array
// would be read past its lifetime.
FOREIGN_DECL(Text, Root_Files_prim_read_line, int64_t, h, {
    static char buf[256];
    FILE *f = (FILE *)(intptr_t)h;
    if (fgets(buf, 256, f) == NULL) {
        buf[0] = '\0';
    } else {
        size_t n = strlen(buf);
        if (n > 0 && buf[n - 1] == '\n') {
            buf[n - 1] = '\0';
        }
    }
    return buf;
})

// prim_close : FILE -> Unit
FOREIGN_DECL(Value, Root_Files_prim_close, int64_t, h, {
    fclose((FILE *)(intptr_t)h);
    return VUnit();
})
