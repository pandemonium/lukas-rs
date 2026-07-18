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
FOREIGN_DECL(int64_t, Root_Files_prim_open, Text, path, Text, mode, {
    return (int64_t)(intptr_t)fopen(path, mode);
})

// prim_write_line : FILE -> Text -> Unit
FOREIGN_DECL(Value, Root_Files_prim_write_line, int64_t, h, Text, line, {
    FILE *f = (FILE *)(intptr_t)h;
    fputs(line, f);
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
