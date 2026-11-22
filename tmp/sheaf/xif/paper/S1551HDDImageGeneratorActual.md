# S1551: actual HDD image generator family, or the precise first missing datum

Date: 2026-10-31. Lean file: tmp/sheaf/xif/paper/S1551HDDImageGeneratorActual.lean.
Companion of S1513 (S1513ImageGeneratorFamily) and S1500 (target structure).

## Verdict

Status label (coord/XI_F_ORIGINAL_ROUTE.md section 12): **[MISSING]** at paper
level, with a **[REDUCTION]**, a degenerate **[BUILT]** actual instance, a
non-free **[BUILT]** witness, and several **[PROVED]** structural facts.

The paper-level S1513ImageGeneratorFamily is NOT filled.  The S1402 source
image is an abstract field; the only actual local-field-valued image family in
the imported donor chain is the output-independent SHE unit-section reading
image.  It does fill S1513ImageGeneratorFamily for the actual source built from
it, but the induced lattice is provably exactly the output-independent free
lattice O_v^2 = s1476LocalLattice 2 v.  This is proved, not asserted, and is
the precise sense in which the available actual image cannot be the paper
object.

## What is constructed / proved

1.  [REDUCTION] The S1513 two-point family is exactly one point per output and
    place:
      Nonempty (S1513ImageGeneratorFamily D)
        <-> forall o v, exists x in D.image o, x v in O_v and x v != 0.
    The single-point record S1551IntegralImagePoint D has an equivalent
    Nonempty type (S1513ImageGeneratorFamily is the same missing datum as one
    integral nonzero image point per output and place).

2.  [CONDITIONAL] Given S1551IntegralImagePoint D, the S1500 target with the
    actual image generator is built: s1551BindingOfPointFamily,
    s1551S1500OfPointFamily; its imageGenerator is exactly the chosen actual
    image point.

3.  [BUILT] The actual SHE 1-column reading image (S1417.outputReadingImage,
    the singleton of the unit-section point) gives an actual source
    s1551UnitImageSource and an actual generator family s1551UnitGeneratorFamily.
    Coordinates are integral (= 1) and nonzero.

4.  [PROVED] Degeneracy of that actual fill:
    * every generator family over the actual reading image is the unit reading
      point (s1551UnitImage_gen_eq);
    * its diagonal lattice is exactly s1476LocalLattice 2 v, for the canonical
      family and for every generator family (s1551UnitLattice_eq_free,
      s1551UnitLattice_any_eq_free);
    * the actual image is output-independent (s1551UnitImage_output_independent,
      s1551UnitImage_not_output_dependent);
    * hence the S1500 target built from it carries the free lattice
      (s1551UnitS1500Lattice_eq_free).

5.  [PROVED] The det (x) M bookkeeping cannot be the missing input:
    replacing detData does not change the generator-family type
    (s1551Nonempty_generatorFamily_replaceDet), and the actual reading source
    and S1513's non-integral singleton source have the same detData with
    opposite generator status (s1551SameDetData_oppositeStatus).

6.  [PROVED] Singleton integrality criterion:
      Nonempty (S1513ImageGeneratorFamily (s1513SingletonSource x hx det))
        <-> forall v in s, x v in O_v.
    This completes S1513's one-directional non-integral obstruction.

7.  [BUILT + PROVED] The generator structure is not a disguised free lattice.
    The actual uniformizer q-candidates of the completed DVRs at the rational
    places (LocalQParameter) give an actual point
    s1551UniformizerPoint that is integral and nonzero at every place with
    valuation below one.  The singleton source s1551UniformizerSource admits
    the genuine generator family s1551UniformizerGeneratorFamily, and its
    diagonal lattice is provably NOT s1476LocalLattice 2 v
    (s1551UniformizerLattice_ne_free: the vector with first coordinate 1 is
    not in it, because q * a = 1 with a integral is impossible for a
    uniformizer).  Therefore the free-lattice collapse is a property of the
    available SHE reading image, not of S1513ImageGeneratorFamily.  This is an
    under-specification witness, not the paper object.

8.  [MISSING] The precise first missing structure is recorded as
    S1551HDDPaperImageGenerator: an actual output-dependent HDD source
    (S1417's missing image family, no inhabitant in the donor chain) plus one
    integral nonzero image point at every output and place, with output
    dependence of the image as a necessary condition.  No inhabitant is
    asserted.  s1551PaperImageGenerator_not_unitImage proves the actual
    reading image cannot supply the output-dependence condition.

## HDD theta/det audit

* det side: S1422HDDDetActual.dependentDetDataOfChar is a
  DetTensorPowerLogVolumeBookkeeping (Set point): region-level log-volume and
  det (x) M scaling laws only, no point-valued field.  S1551 proves its
  irrelevance to the generator family (items 5).
* theta side: PaperC3TensorBlockActual has actual theta image points
  (paperQParameterImagePoint, zero label = 1) integral in the canonical unit
  reference under the norm condition
  (paperQParameterImagePoint_mem_unitReference_of_norm_le_one).  But that
  carrier is ArithmeticTensorTupleBlock over CommonPrimeCompletion places of
  an OriginalInput, not the S1402 dependent product over rational places; that
  file never mentions Theorem311Output, and the paper tree has no map
  Theorem311Output -> SignedLabel.  S1417 already records that no
  Input/OriginalInput place bridge exists.  Hence the theta image cannot be
  transported into S1402 image o for any output o.

## No fake

No sorry, axiom, True/PUnit gate, rank-one surrogate or constant image is used
as the paper object.  The output-independent free lattice appears only as the
proved value of the degenerate actual image (and the non-free witness proves
the generator structure itself is not the free lattice).  The actual source is
built from the actual SHE reading map; no arbitrary data replace the paper
image.

## Verification

Command:
  lake env lean -j1 -R "D:\lean" -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1551HDDImageGeneratorActual.olean tmp/sheaf/xif/paper/S1551HDDImageGeneratorActual.lean
EXIT=0.

Source SHA256: CD533182E2F18CB1C013787D5B013842667BC14E637BCA737A90374442E20A73
Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1551HDDImageGeneratorActual.olean
Olean size: 658328 bytes
Olean SHA256: ABA23942D0208FC692C845993C5CE6C8AF86DDA3C4521FDD76A233CA3B540FB8

Source lines: 696 (including blank lines; 615 non-blank).

Axiom audit (#print axioms on the main declarations, including the non-free
witness): propext, Classical.choice, Quot.sound only.
