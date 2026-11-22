# S1988: H-comparison naturality -- the S1970/S1956 first missing is closed

Date: 2026-11-01.
Source: tmp/sheaf/xif/paper/S1988HComparisonNaturalityActual.lean
Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1988HComparisonNaturalityActual.olean
Compile: lake env lean -j1 -R D:\lean -o <olean> <source>
EXIT: 0 (no errors, no warnings)
Import re-check: EXIT 0 (scratch module importing the olean; scratch removed).
Axiom audit: propext, Classical.choice, Quot.sound only, for every declaration.

SHA256 source: 6E7A1BBECE9E26B73477F681FB2689CF433E0CB3C06400122AE74CBA21BBE280
SHA256 olean: F49D106117E93A96A1C5A0BBFDDD6756E208751B212EBF3BB813E737D7F130D0

## What is proved

The componentwise associativity/cancellation that S1970 left open is completed.

1. Two generalized coherence identities at an arbitrary composite comparison:
   * natCompInvApp_comp_mapComp'  (S1935 natCompInvApp_comp for F.mapComp' f g fg h)
   * natCompHomApp_comp_mapComp'  (S1935 natCompHomApp_comp for F.mapComp' f g fg h)
   Both are proved from the S1935 identities by cases h and mapComp'_eq_mapComp.

2. S1988HComponent_naturality_core: for an arbitrary strong transformation
   alpha : F --> G of pseudofunctors LocallyDiscrete Site^op --> Cat, the
   conjugation of a section by the naturality comparison of alpha is compatible
   with the restrictions along a composable pair of site morphisms.  The proof
   is the componentwise associativity/cancellation:
   * the inverse-direction f.map coherence at the source,
   * the naturality of the middle q-comparison,
   * the hom-direction f.map coherence at the target,
   with the inverse comparisons cancelled against the comparisons via
   Cat.Hom2.comp_app.

3. S1988HComponent and S1988HComponent_naturality: the generic H-comparison is
   natural with respect to the pullHom restrictions of the hom presheaves.

4. The two concrete H-comparisons of S1956 are definitionally the generic
   component for f.map and g.map:
   * S1956FstToHComponent_eq
   * S1956SndToHComponent_eq
   Consequently:
   * S1988FstToHNaturality  : S1956FstToHNaturality f g M N
   * S1988SndToHNaturality  : S1956SndToHNaturality f g M N
   * S1988HComparisonNaturalityAll : S1956HComparisonNaturalityAll
   * S1988S1970HComparisonNaturalityAll : S1970HComparisonNaturalityAll

5. The S1970 consumer is instantiated:
   S1988HComparisonNaturalityAll_gives_natTrans : the two H-comparisons assemble
   into natural transformations of hom presheaves.

## Exact next missing

The prestack half S1956IsoCommaPrestack f g remains the next target.  Given the
naturality proved here, the precise remaining formal step is:

  identify P.presheafHom M N (P = sitePseudofunctor f g) with the fibre product
  of A.presheafHom M.left N.left and B.presheafHom M.right N.right over the
  C-hom presheaf, using the two H-comparison natural transformations, and
  deduce the sheaf condition from the sheaf conditions of the three corner
  presheaves (the three stacks are prestacks).

This pullback-of-sheaves step is not formalized in this file; the target
S1956IsoCommaPrestack is not asserted.  The effectivity half
S1956IsoCommaEffectivity is likewise untouched.  The file defines
S1988NextMissingPrestack (definitionally S1956IsoCommaPrestack) as the named
next target, with no inhabitant.

## Honest boundary

No sorry, no axiom, no Shrink/ULift/PUnit, no fake naturality, no change of the
target.  The only axioms used are propext, Classical.choice and Quot.sound.
