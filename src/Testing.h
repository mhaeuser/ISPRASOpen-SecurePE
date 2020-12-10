/** @file
  Exposes testing functions for the PE/COFF Image Loader. Do not include in
  production code.
  
  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef TESTING_H
#define TESTING_H

RETURN_STATUS
PeCoffTestLoadFull (
  IN VOID    *FileBuffer,
  IN UINT32  FileSize
  );

BOOLEAN
HashUpdate (
  IN OUT  VOID        *HashContext,
  IN      CONST VOID  *Data,
  IN      UINTN       DataLength
  );

#endif // TESTING_H
