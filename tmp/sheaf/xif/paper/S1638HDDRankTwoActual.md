# S1638: faithful HDD rank-two O_v-lattice family, or exact first missing structure

Date: 2026-10-31. Lean file: tmp/sheaf/xif/paper/S1638HDDRankTwoActual.lean.
Imports: S1551HDDImageGeneratorActual, S1630HDDOutputImageActual.

## Verdict

[BUILT] conditional faithful rank-two family from the actual S1402 image
integral generator family.

[PROVED] the exact non-collapse criterion: the image-generated diagonal
lattice equals the S1476 free lattice at a place iff both generator values are
units of O_v.

[PROVED] the available actual SHE unit-section reading image gives exactly the
S1476 free lattice and is output-independent.

[BUILT] a non-free actual witness from the uniformizer q-candidates; it is
output-independent and therefore also not the paper image.

[MISSING] the exact first missing structure: an actual S1402 source whose
image is output-dependent and contains one integral nonzero point at every
output and place.  No inhabitant is asserted.

## Constructed declarations

* S1638HDDRankTwoFamily: an S1402 source plus an actual
  S1513ImageGeneratorFamily.  Its lattice is the diagonal O_v-span of the two
  actual image values:
    F.lattice o v = s1513DiagonalLattice F.generator o v.
* F.basis: an explicit O_v-basis of F.lattice o v, with
  (F.basis o v i : Fin 2 -> Completion v.1) = s1513GeneratorVector ... i.
  Thus the basis vectors are the actual image values placed in their
  coordinates, not an abstract free basis.
* F.basis_linearIndependent, F.lattice_finrank = 2,
  F.lattice_finrank_gt_one: the basic component has rank > 1.
* F.lattice_free, F.lattice_finite, F.lattice_integral,
  F.lattice_span_eq_top: free, finite, integral and full in K_v^2.
* F.lattice_eq_span: the lattice is exactly the O_v-span of the two actual
  image values.
* F.toS1500: the S1500OutputDependentHDDLattice target with the actual image
  generator; its finrank is 2 and its imageGenerator is the actual image
  point.

## Non-collapse criterion

For F : S1638HDDRankTwoFamily and every output o and place v,

  F.lattice o v = s1476LocalLattice 2 v.1
    <-> forall i : Fin 2, IsUnit (s1513LocalGenerator F.generator o v i).

This is F.lattice_eq_free_iff.  The forward direction uses
Pi.single i 1 in the free lattice; the reverse direction writes a free vector
as q_i * (q_i^{-1} * b_i).  A non-unit generator value gives
F.lattice_ne_free_of_not_isUnit.

Consequences:

* S1638UnitFamily (actual SHE reading image): lattice exactly
  s1476LocalLattice 2 v, and source.image is output-independent.  Hence the
  actual reading image cannot supply the missing structure
  (s1638UnitImage_not_firstMissing).
* S1638UniformizerFamily (actual q-candidates): lattice provably different
  from the free lattice (s1638UniformizerFamily_ne_free).  Its image is a
  constant singleton, so it is a non-free witness, not the paper object
  (s1638UniformizerFamily_output_independent).

## Exact first missing structure

S1638FirstMissing I s is the Prop

  exists D : S1402DependentHDDSource I s,
    (exists o o', D.image o != D.image o') and
    (forall o v, exists x in D.image o,
      x v in CompletionIntegers v and x v != 0).

S1638HDDPaperImage bundles the same data with the source.

Proved:

* s1638FirstMissing_iff_generator: S1638FirstMissing I s iff
  Nonempty (S1551HDDPaperImageGenerator I s).  Thus this is exactly S1551's
  first missing structure, not a new weaker surrogate.
* s1638FirstMissing_iff_exists_rankTwoFamily: S1638FirstMissing I s iff there
  is an output-dependent faithful rank-two family.
* s1638FirstMissing_sufficient: the missing structure constructs the faithful
  rank-two family and an inhabitant of the S1500 target.
* s1638FirstMissing_of_s1630: S1630's output-dependent integral point family
  is a sufficient stronger form.
* s1638S1500Target_not_force_output_dependence: the S1500 target alone is
  inhabited by the output-independent free lattice for every source, so the
  target does not force the actual image-generated family.
* s1638FirstMissingContent_replaceDet: replacing the det bookkeeping does not
  change the first-missing content.  S1551 additionally proves an
  opposite-status example with the same det data.

The actual first missing is therefore not the free lattice, not the unit
reading image, and not the det bookkeeping.  It is the output-dependent
integral image-point datum.

## No fake

No sorry, axiom, True/PUnit gate, rank-one replacement or arbitrary Set
surrogate is used.  The S1476 free lattice appears only in the proved
degeneracy statement and the exact non-collapse criterion; the constructed
lattice is always s1513DiagonalLattice of the actual image generators.

Axiom audit of the main declarations:
propext, Classical.choice, Quot.sound only.

## Verification

Command:

  lake env lean -j1 -R "D:\lean" -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1638HDDRankTwoActual.olean tmp/sheaf/xif/paper/S1638HDDRankTwoActual.lean

EXIT=0.

Source: tmp/sheaf/xif/paper/S1638HDDRankTwoActual.lean, 31882 bytes,
724 lines including blank lines (626 non-blank).
Source SHA256: EC2BF157F66E27AECDDFE675D2DEAA43169605248321E998F42222464B21E242
Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1638HDDRankTwoActual.olean
Olean size: 631200 bytes.
Olean SHA256: 7824EFDD1E54CB5048DE7B8D8C24730A7077977AAB631001171BE57366A71415

statement_compiles: YES
proof_body_checked: YES (kernel accepted the olean)
kernel_closed: YES (no sorryAx; standard three axioms)
target_accepted: not claimed; this is a conditional faithful construction plus
the exact first missing structure, not an unconditional paper-level HDD image.
