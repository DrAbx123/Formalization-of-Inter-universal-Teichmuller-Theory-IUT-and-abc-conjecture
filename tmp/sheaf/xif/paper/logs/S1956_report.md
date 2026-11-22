# S1956: IsStack for the actual iso-comma site pseudofunctor -- exact first missing

Date: 2026-11-01.
Source: tmp/sheaf/xif/paper/S1956IsoCommaStackActual.lean
Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1956IsoCommaStackActual.olean

## Verification

- Build command:
  lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1956IsoCommaStackActual.olean tmp/sheaf/xif/paper/S1956IsoCommaStackActual.lean
- EXIT=0, no errors, no warnings.
- Source: 21666 bytes, 454 lines,
  SHA256 B523F896ACF652CC780BDEDF368A3DA0A655AD6E08F13AAA9BA942630008C19C.
- Olean: 372648 bytes,
  SHA256 CBE2A0D6EA839AA09791B86F0E529F64BC585BDF8414D18973FD94BEFE68997B.
- Import re-check: EXIT=0 (a scratch module imports the built olean and
  #checks the main declarations; it reports the expected types).
- Axiom audit (#print axioms on all main declarations): only
  [propext, Classical.choice, Quot.sound].  No sorryAx, no axiom declaration.
- Source scan: no actual sorry/admit tactic and no axiom declaration.  The
  only occurrence of the word "sorry" is in the honesty paragraph.

## What is proved unconditionally

1. S1956IsoCommaStack_iff_prestack_effectivity: for every cospan, the IsStack
   condition for the actual site pseudofunctor of S1945 is exactly the
   conjunction of (a) the prestack condition and (b) essential surjectivity of
   toDescentData for every covering sieve.

2. The first and second leg projections of the hom presheaf:
   S1956FstHomPresheaf : P.presheafHom M N --> A.source.fiber.presheafHom M.left N.left
   S1956SndHomPresheaf : P.presheafHom M N --> B.source.fiber.presheafHom M.right N.right
   with naturality proved from the strict projection formulas for
   sitePseudofunctor_map, mapComp' and mapComp'_inv.  These are the
   descent-of-morphisms maps for the two legs.

3. The candidate H-comparison component functions
   S1956FstToHComponent and S1956SndToHComponent, obtained by applying
   f.map / g.map and the naturality comparisons S1864SiteComparisonLeft /
   S1864SiteComparisonRight.

4. Consumers: S1956IsoCommaStack_to_S1891 and S1956IsoCommaStack_core show
   that the target supplies S1891's existence form and S1864's stack half
   with the canonical pseudofunctor itself.  S1956IsoCommaStack_gives_stack_field
   packages the canonical EtaleStackOverField and its fiber equivalences.

## Exact first missing

(A) S1956HComparisonNaturalityAll: the componentwise naturality of the two
    H-comparison maps (S1956FstToHNaturality and S1956SndToHNaturality) with
    respect to the presheaf restriction maps.  This is the strong-transformation
    coherence of f.map and g.map with the mapComp of the three stacks.
    Once this holds, the hom presheaf of the iso-comma is the pullback of the
    F-, G- and H-hom presheaves; the three corners are sheaves, so the
    iso-comma is a prestack.

(B) S1956IsoCommaEffectivity: essential surjectivity of toDescentData for
    every covering sieve, i.e. the object-level 2-limit interchange for the
    triple of descent data.

Neither (A) nor (B) is inhabited in the file.  The pullback-of-sheaves
argument from (A) and the descent-data comparison from (B) are explicitly
recorded as the next formal steps and are not asserted as theorems.

## Honest boundary

No fake IsStack, no sorry, no new axiom, no Shrink/ULift/PUnit, no change of
the target.  S1956IsoCommaStack is a named Prop with no inhabitant asserted.
The file proves the reduction of the target to (A)+(B), the two leg
projections, and the H-comparison components; the two remaining 2-categorical
coherences are named exactly.
