/* Minimal smack.h stub for cbmc-native backend.
 *
 * The real SMACK toolchain provides this header with __VERIFIER_* declarations.
 * When running cbmc directly (bypassing SMACK), we provide stubs so that
 * #include "smack.h" in the harnesses succeeds.  The actual __VERIFIER_*
 * calls are remapped to CBMC primitives via -D flags passed on the command
 * line by run_pipeline.py's cbmc-native backend.
 *
 * Guard each declaration with #ifndef so that command-line -D macro
 * definitions (which arrive before header processing) take precedence
 * and do not conflict with the function-like declarations here.
 */

#ifndef SMACK_H_
#define SMACK_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#ifndef __VERIFIER_nondet_int
int            __VERIFIER_nondet_int(void);
#endif
#ifndef __VERIFIER_nondet_long
long           __VERIFIER_nondet_long(void);
#endif
#ifndef __VERIFIER_nondet_uint
unsigned int   __VERIFIER_nondet_uint(void);
#endif
#ifndef __VERIFIER_nondet_ulong
unsigned long  __VERIFIER_nondet_ulong(void);
#endif
#ifndef __VERIFIER_nondet_u64
uint64_t       __VERIFIER_nondet_u64(void);
#endif
#ifndef __VERIFIER_nondet_char
char           __VERIFIER_nondet_char(void);
#endif
#ifndef __VERIFIER_nondet_uchar
unsigned char  __VERIFIER_nondet_uchar(void);
#endif
#ifndef __VERIFIER_nondet_pointer
void *         __VERIFIER_nondet_pointer(void);
#endif

#ifndef __VERIFIER_assume
void __VERIFIER_assume(int expr);
#endif
#ifndef __VERIFIER_assert
void __VERIFIER_assert(int expr);
#endif
#ifndef __VERIFIER_error
void __VERIFIER_error(void);
#endif

#ifdef __cplusplus
}
#endif

#endif /* SMACK_H_ */
