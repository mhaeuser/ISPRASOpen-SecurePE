/** @file
  Implements testing code for fuzztesting. Do not include in production code.
  
  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "BasePeCoffLibInternals.h"

#include "Frama.h"
#include "PeCoffInit.h"
#include "PeCoffLoad.h"
#include "PeCoffRelocate.h"

#include "Testing.h"

#include <stdint.h>
#include <stdio.h>

BOOLEAN PcdImageLoaderRtRelocAllowTargetMismatch = TRUE;
BOOLEAN PcdImageLoaderHashProhibitOverlap = TRUE;
BOOLEAN PcdImageLoaderLoadHeader = TRUE;
BOOLEAN PcdImageLoaderSupportArmThumb = TRUE;
BOOLEAN PcdImageLoaderForceLoadDebug = TRUE;
BOOLEAN PcdImageLoaderTolerantLoad = TRUE;
STATIC UINT64  PcdValidAllocMask = MAX_UINT64;
STATIC UINT8 PcdValidHashes = MAX_UINT8;
BOOLEAN PcdImageLoaderSupportDebug = TRUE;
UINTN HashDependency;

BOOLEAN
HashUpdate (
  IN OUT  VOID        *HashContext,
  IN      CONST VOID  *Data,
  IN      UINTN       DataLength
  )
{
  CONST UINT8 *D = (CONST UINT8 *)Data;

  (VOID) HashContext;

  for (UINTN i = 0; i < DataLength; i++)
    HashDependency += D[i];

  if (PcdValidHashes > 0) {
    PcdValidHashes--;
    return TRUE;
  }

  return FALSE;
}

static uint8_t *readFile(const char *str, uint32_t *size) {
  FILE *f = fopen(str, "rb");

  if (!f)
    return NULL;

  fseek(f, 0, SEEK_END);
  long fsize = ftell(f);
  if (fsize < 0 || fsize > MAX_UINT32) {
    fclose(f);
    return NULL;
  }

  fseek(f, 0, SEEK_SET);

  uint8_t *string = aligned_alloc(8, (fsize + 7U) & ~7U);
  if (fread(string, (size_t) fsize, 1, f) != 1)
    abort(); 

  fclose(f);

  *size = (uint32_t) fsize;

  return string;
}

void *TestMalloc4K(size_t x) {
  if (x >= 1024*1024)
    return NULL;

  void *p = NULL;

  if (PcdValidAllocMask & BIT0)
    p = aligned_alloc(4096, (x + 4095) & ~4095U);

  PcdValidAllocMask >>= 1U;
  return p;
}

void *TestMalloc(size_t x) {
  if (x >= 1024*1024)
    return NULL;

  void *p = NULL;
  if (PcdValidAllocMask & BIT0)
    p = malloc(x);

  PcdValidAllocMask >>= 1;
  return p;
}

static void loadConfig(const uint8_t *data, size_t size) {
  PcdImageLoaderRtRelocAllowTargetMismatch = (data[size - 1] & 1U) != 0;
  PcdImageLoaderHashProhibitOverlap = (data[size - 1] & 2U) != 0;
  PcdImageLoaderLoadHeader = (data[size - 1] & 4U) != 0;
  PcdImageLoaderSupportArmThumb = (data[size - 1] & 8U) != 0;
  PcdImageLoaderForceLoadDebug = (data[size - 1] & 16U) != 0;
  PcdImageLoaderTolerantLoad = (data[size - 1] & 32U) != 0;
  PcdImageLoaderSupportDebug = (data[size - 1] & 64U) != 0;
  memcpy(&PcdValidAllocMask, &data[size - MIN(size, sizeof(UINT64))], MIN(size, sizeof(UINT64)));
  PcdValidHashes = data[size - MIN(size, sizeof(UINT64) + sizeof(UINT8))];
}

#ifdef FUZZING

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  if (size == 0)
    return 0;
  void *p = aligned_alloc(8, (size + 7) & ~7U);
  if (p != NULL) {
    loadConfig(data, size);
    memcpy(p, data, size);
    PeCoffTestLoadFull(p, size);
    free(p);
  }
  return 0;
}

#else

int main(int argc, char *argv[]) {
  if (argc < 2)
    return 1;
  uint32_t size;
  uint8_t *data = readFile(argv[1], &size);
  if (data != NULL) {
    if (size > 0) {
      loadConfig(data, size);
      PeCoffTestLoadFull(data, size);
    }

    free(data);
  }
  return 0;
}

#endif
