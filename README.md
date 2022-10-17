SecurePE
========

This repository contains the reimplementation of the EDK II Image Loader
for UEFI environments and the ACSL annotations for its formal verification.

The specifications are developed in the [ACSL](https://frama-c.com/html/acsl.html)
language. Frama-C with [AstraVer](https://forge.ispras.ru/projects/astraver) plugin
is used as the deductive verification tool.

### Papers

M. Häuser and V. Cheptsov, "Securing the EDK II Image Loader," 2020 Ivannikov Ispras Open Conference (ISPRAS), 2020, pp. 16-25, DOI: [0.1109/ISPRAS51486.2020.00010](https://doi.org/10.1109/ISPRAS51486.2020.00010). [[ArXiv preprint]](https://arxiv.org/abs/2012.05471)


### Errata
* The publication has incorrectly defined `A_MAX = 4` for the IA32 architecture. The correct definition is `A_MAX = 8`. This furthermore implies that `_Alignof(UINT64) = 8` for IA32 architectures. This does not affect the result of the verification.
* The code snapshot has incorrectly defined `RelocsStripped = (TeHdr->DataDirectory[0].Size > 0)` for TE Images. The correct definition is `RelocsStripped = (TeHdr->DataDirectory[0].Size == 0)`. This bug effectively prevents the Image relocation of TE Images. This does not affect the safety or well-defined behaviour of the code snapshot.
* The code snapshot may incorrectly handle runtime relocation. If an absolute relocation is encountered, the accesses to the `FixupData` array may de-sync, as the index is not incremented corrected (see [src/PeCoffRelocate.c:1570](https://github.com/mhaeuser/ISPRASOpen-SecurePE/blob/beec1e67505407d14c950c425cf064e3ff915ba7/src/PeCoffRelocate.c#L1570)). This does not affect the safety or well-defined behaviour of the code snapshot.
