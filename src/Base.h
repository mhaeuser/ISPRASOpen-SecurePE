/** @file
  Provides minimal compatibility between the C Standard Library and EDK II.

  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef BASE_H
#define BASE_H

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef uint8_t  UINT8;
typedef char     CHAR8;
typedef uint16_t UINT16;
typedef uint32_t UINT32;
typedef uint64_t UINT64;
typedef uint64_t   UINTN;
typedef _Bool    BOOLEAN;
typedef UINT16   CHAR16;

#define EFIAPI
#define IN
#define OUT
#define OPTIONAL
#define CONST const
#define STATIC static
#define VOID void
#define TRUE 1
#define FALSE 0

#define BASE_4KB 4096U
#define MAX_UINT64 0xFFFFFFFFFFFFFFFFU
#define MAX_UINTN MAX_UINT64
#define MAX_UINT32 0xFFFFFFFFU
#define MAX_UINT16 0xFFFFU
#define MAX_UINT8  0xFFU

typedef UINTN RETURN_STATUS;
#define ENCODE_ERROR(StatusCode)     ((RETURN_STATUS)(0x8000000000000000 | (StatusCode)))
#define RETURN_SUCCESS               0
#define RETURN_UNSUPPORTED           ENCODE_ERROR (3)

#ifndef PRODUCTION
  #include "Frama.h"
  
  /*@ assigns \nothing;
    @ ensures \result != \null <==> \fresh(\result, n);
    @ ensures is_aligned_N (pointer_to_address (\result), BASE_4KB);
  */
  extern void *malloc4K (size_t n);

  #define AllocatePool4K malloc4K
  #define AllocatePool   malloc
#else
  void *TestMalloc4K(size_t x);
  void *TestMalloc(size_t x);
  #define AllocatePool4K  TestMalloc4K
  #define AllocatePool    TestMalloc
#endif
#define FreePool      free

#define CopyMem        memmove
#define SetMem(a,b,c)  memset(a,c,b)
#define ZeroMem(a,b)   SetMem(a,b,0)

#define OFFSET_OF(TYPE, Field) __builtin_offsetof(TYPE, Field)

#define BIT0  ((uint32_t) 1U << (uint32_t) 0U)
#define BIT10 ((uint32_t) 1U << (uint32_t) 10U)
#define BIT11 ((uint32_t) 1U << (uint32_t) 11U)
#define BIT25 ((uint32_t) 1U << (uint32_t) 25U)
#define BIT26 ((uint32_t) 1U << (uint32_t) 26U)

#define EFI_PAGE_SIZE BASE_4KB

#define IS_POW2(v)        ((v) != 0 && ((v) & ((v) -/*@%*/ 1U)) == 0)
#define ALIGN_VALUE(v, a) (((v) + ((a) -/*@%*/ 1U)) & ~((a) -/*@%*/ 1U))

#define IS_ALIGNED(v, a)  (((v) & ((a) -/*@%*/ 1U)) == 0U)

#define MIN(a, b)  \
  (((a) < (b)) ? (a) : (b))

extern BOOLEAN PcdImageLoaderRtRelocAllowTargetMismatch;
extern BOOLEAN PcdImageLoaderHashProhibitOverlap;
extern BOOLEAN PcdImageLoaderLoadHeader;
extern BOOLEAN PcdImageLoaderSupportArmThumb;
extern BOOLEAN PcdImageLoaderSupportDebug;
extern BOOLEAN PcdImageLoaderForceLoadDebug;
extern BOOLEAN PcdImageLoaderTolerantLoad;

#define PcdGetBool(TokenName)               TokenName

#endif // BASE_H
