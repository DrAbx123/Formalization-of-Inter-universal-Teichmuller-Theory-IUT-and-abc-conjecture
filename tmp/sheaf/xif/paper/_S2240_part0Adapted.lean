/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S2240
-/

import tmp.sheaf.xif.paper.S2185ConcreteTwoPullbackActual
import tmp.sheaf.xif.paper.S1852CoherentCoverActual
import tmp.sheaf.xif.paper.S1850RefuteS1756Actual
import tmp.sheaf.xif.paper.S2100GPresentationConeEssSurjActual
import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S1844PointSeparatedActual


/-!
# S2240: the exact coherence boundary of the S2185 strict-cone comparison

## The question

S2185 reduced the S2130 concrete two-pullback to the single 2-cell statement
S2185StrictConeIso: for every cone c over the base square, the two strong
transformations

  (S2130PB).isPullback.lift W c ; y(S2130Phi)   and   c.toY ; y(S2130Graph)

into y(C x_X T) are 2-isomorphic.  Since the target is a representable stack, such
an isomorphism is equivalent to an equality of the underlying scheme morphisms at
every test object; the issue is producing one.

This file determines exactly what that statement needs.  It does not assert
S2185StrictConeIso, and it does not fake a witness.

## What is proved

1. S2240StrictConeIsoAt (and its uniform form S2240StrictConeIso_of_coneEssSurj):
   if the C-presentation S2130PC carries the full 2-universal property
   (S1852ConeEssSurj, i.e. cone essential surjectivity), then the comparison
   2-cell exists for every cone c.

   The proof is the natural one: both 1-cells are candidates for the lift of
   the transported cone (c.toX ; g.map, c.toY) over the C-presentation square, and
   cone essential surjectivity identifies both with the recorded lift.  The four
   comparison 2-cells are explicit associator/whiskering chains
   (S2240PhiSiteToSource, S2240PhiSiteToProj, S2240GraphSiteToSource,
   S2240GraphSiteToProj), and the scheme maps S2130Phi, S2130Graph are replaced by
   their site forms S2130PhiSite, S2130GraphSite through the 2-Yoneda comparison
   S1742StrongTransIsoOfHom.

2. S2240ConcreteTwoPullback_of_coneEssSurj and S2240Hg_of_coneEssSurj: the S2130
   target and the S2130 base-change presentations follow from the same coherence.

3. S2240ConeEssSurj_doubled_false and S2240NotCPresentationConeEssSurj: the uniform
   coherence hypothesis is FALSE.  At S1850's doubled cover the C-presentation is
   literally S1850Doubled at the identity point, and S1852Doubled_not_coneEssSurj
   shows that it is not cone-essentially-surjective.  Hence the uniform
   S2130ConcreteTwoPullback cannot be closed from this hypothesis, exactly as S2100
   refutes the uniform strong-presentation input and S2094's literal form.

4. The per-cover construction, which is the usable repair: for a strong target cover
   Cs : StrongCover (S1852) and an arbitrary source cover B, the concrete
   two-pullback witness of S2130 exists for every A, f, g, T, ptA
   (S2240WitnessFor_strongCover), and hence so does the S2130 finite-etale
   presentation, with finite etale projection (S2240HgFor_strongCover,
   S2240HgFor_strongCover_finiteEtale).  The same holds for a coherent cover
   (S2240WitnessFor_coherent).  The full witness (lift, both comparisons, action on
   cone morphisms, 2-cell extensionality) is assembled from the S1911 strict-square
   witness and the comparison supplied by the coherence, exactly as in S2185 but
   with the hypothesis localised at the fixed target cover C.

## The exact first missing

S2185StrictConeIso remains unproved, and it is not refuted here.  What is settled:

* Its natural sufficient datum is the cone essential surjectivity of the
  C-presentation, S2240CPresentationConeEssSurj, and that datum is false
  (S2240NotCPresentationConeEssSurj).  So no uniform proof can pass through the
  strong presentation field.
* The missing content is exactly the 2-cell itself, best understood as follows: over
  the C-presentation square the transported cone has two candidate 1-cells, the
  recorded lift and the composite of the cone's test leg with the graph section, and
  the weak witness records no comparison between two candidates for the same cone.
  The gap is therefore the graph-compatibility of the recorded presentation lift.
  No field of EtaleStackBaseChangePresentation supplies it: the weak
  TwoPullbackWitness does not give cone essential surjectivity in general
  (S1801NoGenericEssSurj), the doubled presentation is a genuine weak presentation
  at which it fails (S1850Doubled, S1852Doubled_not_coneEssSurj), and S2123 shows
  that the strong field is vacuous at the recorded lift, the missing comparison
  being a coherent lift cone morphism (the presentation twist) of the same form.
* The repair used by the inverse construction is the coherent cover datum: for
  coherent/strong target covers the comparison and the witness are constructed
  here, with no extra assumption.

Consequently the uniform S2130ConcreteTwoPullback over all recorded (possibly
incoherent) covers is not obtained here; the coherent-cover form is, and it is the
form available from the coherent cover datum of S1852.

## Axiom footprint

No sorry, no new axiom, no change of any recorded definition.  Every declaration
below depends only on propext, Classical.choice and Quot.sound.
-/