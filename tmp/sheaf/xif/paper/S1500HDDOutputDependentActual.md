# S1500: output-dependent HDD arithmetic-vector-bundle localization

Date: 2026-10-31. EXIT=0; exact target structure, no fake output-independent bundle.

## Actual pieces

* S1476: actual rank-2 free O_Q^2 localization s1476ActualLocalization /
  s1476LocalLattice; independent of Theorem311Output by construction.
* S1402DependentHDDSource I s: actual output-dependent image family
  image : Theorem311Output I -> Set ((v:s) -> localField v), with compactness,
  nonemptiness, coordinate_nonzero and dependentHull via LocalFieldProductHull.
* S1417ImageFamily I s: same data, equivalent to S1402 source;
  outputReadingImage is actual but output-independent (constant unit reading),
  so it is not used as the HDD image.

## Exact target structure

S1500OutputDependentHDDLattice I s:
  source : S1402DependentHDDSource I s
  lattice : Theorem311Output I -> (v : s) -> Submodule O_v (Fin 2 -> K_v)
  free/finite/finrank=2/integral/full
  imageGenerator : Theorem311Output I -> (v:s) -> Fin 2 -> ((v:s) -> localField v)
  imageGenerator_mem : imageGenerator o v i in source.image o
and S1500FirstField = the output/place-dependent rank-2 lattice family.

No inhabitant is asserted.  The exact first missing structure is the actual
binding of the free rank-2 lattice to the S1402 image: the image is a set of
product-local-field tuples, not a rank-2 O_v-module generator family.

## No fake

The output-independent free lattice is not renamed as the paper HDD lattice;
S1417's outputReadingImage (constant unit reading) is not used as the image.
No True/Nonempty/arbitrary free bundle substitution.

## Verification

EXIT=0; olean generated.
