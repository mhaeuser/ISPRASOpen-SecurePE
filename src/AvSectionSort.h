/** @file
  Declares the lemmas required to prove Image Section sorting by Authenticode.

  Copyright (c) 2020, Marvin Häuser. All rights reserved.<BR>
  Copyright (c) 2020, Vitaly Cheptsov. All rights reserved.<BR>
  Copyright (c) 2020, ISP RAS. All rights reserved.<BR>
  SPDX-License-Identifier: BSD-3-Clause
**/

#ifndef AV_SECTION_SORT_H
#define AV_SECTION_SORT_H

/*@ axiomatic SectsInsertionSort {
  @   predicate SortedSects(EFI_IMAGE_SECTION_HEADER **Sections, integer h) =
  @     \forall integer i, j; 0 <= i <= j < h ==>
  @       Sections[i]->PointerToRawData <= Sections[j]->PointerToRawData;
  @
  @   lemma abs_order_high:
  @     \forall EFI_IMAGE_SECTION_HEADER **Sections, *Section, integer h, i;
  @     (0 <= i < h && SortedSects (Sections, h)) ==>
  @       Section->PointerToRawData <= Sections[i]->PointerToRawData ==>
  @         \forall integer j; i <= j < h ==>
  @           Section->PointerToRawData <= Sections[j]->PointerToRawData;
  @
  @   predicate sects_all_but_one_preserved{L1, L2}(EFI_IMAGE_SECTION_HEADER **SortedSections, integer h, integer e) =
  @     (\forall integer i; (0 <= i < h && i != e) ==>
  @        \at(SortedSections[i], L1) == \at(SortedSections[i], L2));
  @ }
*/

#endif // AV_SECTION_SORT_H
