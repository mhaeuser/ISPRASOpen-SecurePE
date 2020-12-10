/** @file
  Calls all important Image Loader APIs demonstrate fully proven loading.
  Do not include in production code.

  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#include "BasePeCoffLibInternals.h"

#include "BaseOverflow.h"
#include "PeCoffInit.h"
#include "PeCoffHash.h"
#include "PeCoffLoad.h"
#include "PeCoffRelocate.h"
#include "PeCoffDebug.h"

#include "Testing.h"

#include <stdint.h>

/*@ ghost
  @ /@ requires \freeable(Memory);
  @  @ assigns \nothing;
  @  @ ensures pointer_max_aligned(Memory);
  @  @/
  @ void malloc_max_aligned (const void *Memory);
*/

/*@ requires \valid(Context);
  @ requires \typeof(Context->ImageBuffer) <: \type(char *);
  @ requires pointer_max_aligned(Context->ImageBuffer);
  @ requires image_context_reloc_info_sane (Context);
  @
  @ requires !Context->RelocsStripped;
  @ requires image_reloc_dir_mem_valid ((char *) Context->ImageBuffer, Context->SizeOfImage, Context->RelocDirRva, Context->RelocDirSize);
  @
  @ requires !Context->RelocsStripped;
  @
  @ assigns ((char *) Context->ImageBuffer)[0 .. Context->SizeOfImage - 1];
*/
STATIC
RETURN_STATUS
PeCoffTestRtReloc (
  PE_COFF_IMAGE_CONTEXT  *Context
  )
{
  RETURN_STATUS                   Status;
  PE_COFF_RUNTIME_CONTEXT *RtCtx;
  UINT32                         RtCtxSize;

  /*@ assigns Status, RtCtxSize;
    @ ensures Status == RETURN_SUCCESS <==> RtCtxSize == image_context_runtime_fixup_size (Context);
  */
  Status = PeCoffRelocationDataSize (Context, &RtCtxSize);

  /*@ assigns \nothing;
    @ ensures RtCtxSize == image_context_runtime_fixup_size (Context);
  */
  if (Status != RETURN_SUCCESS) {
    return RETURN_UNSUPPORTED;
  }

  /*@ assigns RtCtx;
    @ ensures RtCtx != \null ==>
    @           \valid(RtCtx) &&
    @           \valid(RtCtx->FixupData + (0 .. image_context_runtime_fixup_num (Context) - 1));
  */
  RtCtx = AllocatePool (RtCtxSize);

  /*@ assigns \nothing;
    @ ensures RtCtx != \null;
    @ ensures \valid(RtCtx) &&
    @         \valid(RtCtx->FixupData + (0 .. image_context_runtime_fixup_num (Context) - 1));
  */
  if (RtCtx == NULL) {
    return RETURN_UNSUPPORTED;
  }

  /*@ assigns ((char *) Context->ImageBuffer)[0 .. Context->SizeOfImage - 1];
    @ assigns RtCtx->RelocDirRva;
    @ assigns RtCtx->RelocDirSize;
    @ assigns RtCtx->FixupData[0 .. (RtCtxSize - sizeof (PE_COFF_RUNTIME_CONTEXT)) / sizeof (UINT64) - 1];
  */
  Status = PeCoffRelocateImage (Context, 0x69696969, RtCtx, RtCtxSize);

  //@ assigns \nothing;
  if (Status != RETURN_SUCCESS) {
    /*@ assigns \nothing;
      @ frees RtCtx;
    */
    free (RtCtx);
    return Status;
  }

  //@ assigns ((char *) Context->ImageBuffer)[0 .. Context->SizeOfImage - 1];
  Status = PeCoffRelocateImageForRuntime (Context->ImageBuffer, Context->SizeOfImage, 0x96969696, RtCtx);
  
  /*@ assigns \nothing;
    @ frees RtCtx;
  */
  free (RtCtx);

  return Status;
}

/*@ requires \valid(Context);
  @ requires \typeof(Destination) <: \type(char *);
  @ requires pointer_max_aligned(Destination);
  @ requires pointer_max_aligned(Context->FileBuffer);
  @ requires \valid((char *) Destination + (0 .. DestinationSize - 1));
  @ requires DestinationSize == Context->SizeOfImage + Context->SizeOfImageDebugAdd + Context->SectionAlignment;
  @ requires pointer_aligned (Destination, BASE_4KB);
  @
  @ requires image_context_fields_correct (Context) &&
  @          image_context_hdr_valid (Context) &&
  @          image_context_file_char_valid (Context) &&
  @          image_context_reloc_info_sane (Context) &&
  @          image_context_sects_sane (Context, MAX_UINT32) &&
  @          image_sects_in_image (Context) &&
  @          \typeof (Context->FileBuffer) <: \type (char *) &&
  @          is_pow2_32 (Context->SectionAlignment) &&
  @          0 < image_hdr_virtual_size (Context->SizeOfHeaders, Context->SectionAlignment) &&
  @          Context->SectionsOffset <= MAX_UINT32 &&
  @          0 < Context->NumberOfSections &&
  @          \let Sections         = image_context_get_sections (Context);
  @          \let NumberOfSections = Context->NumberOfSections;
  @          \valid (Sections + (0 .. NumberOfSections - 1));
  @
  @ assigns ((char *) Destination)[0 .. DestinationSize - 1];
  @ assigns Context->ImageBuffer;
  @ assigns Context->RelocDirRva;
  @ assigns Context->RelocDirSize;
*/
STATIC
RETURN_STATUS
PeCoffTestLoad (
  PE_COFF_IMAGE_CONTEXT *Context,
  VOID                  *Destination,
  UINT32                DestinationSize
  )
{
  RETURN_STATUS  Status;
  CHAR8         *PdbPath;
  UINT32        PdbPathSize;

  /*@ assigns Status, ((char *) Destination)[0 .. DestinationSize - 1];
    @ assigns Context->ImageBuffer;
    @ ensures \let AlignOffset = align_up (pointer_to_address (Destination), Context->SectionAlignment) - pointer_to_address (Destination);
    @         Context->ImageBuffer == (char *) Destination + AlignOffset;
  */
  (VOID) PeCoffLoadImage (Context, Destination, DestinationSize);

  /*@ assigns Status, PdbPathSize;
    @ ensures PdbPathSize == 0;
  */
  Status = PeCoffGetPdbPath (Context, &PdbPath, &PdbPathSize);

  //@ assigns \nothing;
  if (Status == RETURN_SUCCESS) {
    ZeroMem (PdbPath, PdbPathSize);
  }

  /*@ assert \let Address     = pointer_to_address (Destination);
    @        \let AlignOffset = align_up (Address, Context->SectionAlignment) - Address;
    @        AlignOffset < Context->SectionAlignment &&
    @        AlignOffset + Context->SizeOfImage <= DestinationSize;
  */

  //@ assigns ((char *) Destination)[0 .. DestinationSize - 1];
  if (!Context->RelocsStripped) {
    /*@ requires \let AlignOffset = align_up (pointer_to_address (Destination), Context->SectionAlignment) - pointer_to_address (Destination);
      @          Context->ImageBuffer == (char *) Destination + AlignOffset &&
      @          AlignOffset + Context->SizeOfImage <= DestinationSize &&
      @          (Context->RelocsStripped ==>
      @            pointer_to_address (Destination) == Context->ImageBase &&
      @            image_base_sane (Context->ImageBase, Context->SectionAlignment) &&
      @            AlignOffset == 0 &&
      @            Context->ImageBuffer == (char *) Destination);
      @ assigns ((char *) Destination)[0 .. DestinationSize - 1];
    */
    if (Context->Subsystem != EFI_IMAGE_SUBSYSTEM_EFI_RUNTIME_DRIVER) {
      //@ assigns ((char *) Context->ImageBuffer)[0 .. Context->SizeOfImage - 1];
      Status = PeCoffRelocateImage (Context, PTR_TO_ADDR (Context->ImageBuffer, 0), NULL, 0);
    } else {
      //@ assigns ((char *) Context->ImageBuffer)[0 .. Context->SizeOfImage - 1];
      Status = PeCoffTestRtReloc (Context);
    }
  }

  //@ assigns \nothing;
  if (Status != RETURN_SUCCESS) {
    return Status;
  }

  /*@ assigns ((char *) Destination)[0 .. DestinationSize - 1];
    @ assigns Context->RelocDirRva;
    @ assigns Context->RelocDirSize;
  */
  PeCoffDiscardSections (Context);

  return RETURN_SUCCESS;
}

/*@ requires \typeof(FileBuffer) <: \type(char *);
  @ requires pointer_max_aligned(FileBuffer);
  @ requires \valid((char *) FileBuffer + (0 .. FileSize - 1));
*/
RETURN_STATUS
PeCoffTestLoadFull (
  IN VOID    *FileBuffer,
  IN UINT32  FileSize
  )
{
  RETURN_STATUS         Status;
  BOOLEAN               Result;
  PE_COFF_IMAGE_CONTEXT Context;
  VOID                  *Destination;
  UINT32                DestinationSize;

  //@ assigns Context;
  Status = PeCoffInitializeContext (&Context, FileBuffer, FileSize);

  //@ assigns \nothing;
  if (Status != RETURN_SUCCESS) {
    return RETURN_UNSUPPORTED;
  }

  UINT8 HashContext;
  //@ assigns \nothing;
  Result = PeCoffHashImage (
             &Context,
#ifdef PRODUCTION
             HashUpdate,
#endif
             &HashContext
             );

  //@ assigns \nothing;
  if (!Result) {
    return RETURN_UNSUPPORTED;
  }

  /*@ assigns DestinationSize;
    @ ensures DestinationSize == Context.SizeOfImage + Context.SizeOfImageDebugAdd;
  */
  DestinationSize = Context.SizeOfImage + Context.SizeOfImageDebugAdd;

  /*@ assigns DestinationSize;
    @ ensures DestinationSize == Context.SizeOfImage + Context.SizeOfImageDebugAdd + Context.SectionAlignment;
  */
  if (BaseOverflowAddU32 (DestinationSize, Context.SectionAlignment, &DestinationSize)) {
    return RETURN_UNSUPPORTED;
  }

  /*@ assigns Destination;
    @ ensures Destination != \null ==>
    @           \valid((char *) Destination + (0 .. DestinationSize - 1));
  */
  Destination = AllocatePool4K (DestinationSize);

  /*@ assigns \nothing;
    @ ensures \valid((char *) Destination + (0 .. DestinationSize - 1));
  */
  if (Destination == NULL) {
    return RETURN_UNSUPPORTED;
  }

  /*@ assigns \nothing;
    @ ensures pointer_max_aligned (Destination);
  */
  //@ ghost malloc_max_aligned (Destination);

  /*@ assigns Status;
    @ assigns ((char *) Destination)[0 .. DestinationSize - 1];
    @ assigns Context.ImageBuffer;
    @ assigns Context.RelocDirRva;
    @ assigns Context.RelocDirSize;
  */
  Status = PeCoffTestLoad (&Context, Destination, DestinationSize);

  /*@ assigns \nothing;
    @ frees Destination;
  */
  free (Destination);

  return Status;
}
