import tmp.sheaf.xif.paper.S2855ChartYDirectedCoverActual
import tmp.sheaf.xif.paper.S2820E37TransitionActual

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S2855ChartYDirectedCoverActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2863ChartYNegationCompatibilityAudit

/-!
## S2863 audit: can hf use existing transition lemmas?

In S2855ChartYDirectedCoverActual, hf has the exact type

  forall x y,
    pullback.fst ((chartYCover K).f x) ((chartYCover K).f y) ≫
        chartYNegGMap K x =
      pullback.snd ((chartYCover K).f x) ((chartYCover K).f y) ≫
        chartYNegGMap K y

This is a compatibility condition for the two chart maps on the pullback
overlap.  It is the hypothesis of chartYNegGluedHom.

Existing S2820 transition API provides:
* curveChartOverlapTransitionRingEquiv and its apply/symm lemmas;
* S2820E37TransitionIso between chart Z and chart Y overlaps;
* E37ChartZOverlapMap / E37ChartYOverlapMap;
* the glued projective scheme built from S2820E37TransitionIso.

It does NOT provide any lemma stating that the negation chart maps g0Scheme
and g1Scheme commute with the overlap transition, nor any pullback square
equality involving chartYNegGMap.  No theorem in the tree mentions
chartYNeg compat/pullback overlap equality.

Conclusion: hf is a genuine extra input.  It cannot be obtained by direct
application of an existing transition lemma.  Proving it would require a new
affine computation: show that the two ring homomorphisms g0Ring and g1Ring
agree after further localization to the overlap, equivalently that the
negation formulas are compatible with S2820E37TransitionIso.  That
compatibility is not formalized.

No fake compatibility proof is introduced.
-/

#check chartYCover
#check chartYNegGMap
#check chartYNegGluedHom
#check curveChartOverlapTransitionRingEquiv
#check S2820E37TransitionIso

end LeanFormal.IUT.XiFPaper.S2863ChartYNegationCompatibilityAudit
end
