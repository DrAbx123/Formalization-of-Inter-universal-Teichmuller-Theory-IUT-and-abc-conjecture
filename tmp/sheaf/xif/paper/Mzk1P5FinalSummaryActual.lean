import tmp.sheaf.xif.paper.Mzk1P5PhaseExponentDataActual
import tmp.sheaf.xif.paper.Mzk1P5ComparisonDerivedActual
import tmp.sheaf.xif.paper.Mzk1P5CJDerivedActual
import tmp.sheaf.xif.paper.Mzk1P5RootChoiceOrderActual
import tmp.sheaf.xif.paper.Mzk1P5HunitDerivedActual
import tmp.sheaf.xif.paper.Mzk1P5QNormalizationInputActual

/-!
# P5 final conditional summary

All remaining named inputs are collected in P5NamedInputs:
* toRoot : L ->+* RootExtension G v0 (analytic field map),
* r : L (analytic root),
* root_image : toRoot r = twoLthRootAt^l,
* phase : PhaseExponentData l (label-to-mu2l-exponent map).

The c_j and the comparison are NOT inputs: cOfPhase is canonical and
comparison_cOfPhase proves hcomparison.  The final theorem below gives the
actual conditional comparison in terms of these four named inputs only.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P5FinalSummaryActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.Mzk1P5LabelShiftActual
open LeanFormal.IUT.XiFPaper.Mzk1P5BridgeIntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1P5BridgeInstantiateActual
open LeanFormal.IUT.XiFPaper.Mzk1P5ComparisonDerivedActual
open LeanFormal.IUT.XiFPaper.Mzk1P5PhaseExponentDataActual
open LeanFormal.IUT.Foundations.Theta

universe u v

variable {l : PrimeGeFive}
variable {K : Type v} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type*} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
variable (v0 : V)
variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- The four remaining named inputs of the P5 root-unit comparison. -/
structure P5NamedInputs (L : Type u) [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (l : PrimeGeFive) {K : Type v} [Field K] [NumberField K]
    {p : Nat} [Fact p.Prime] {V : Type*} [Fintype V]
    (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
    (v0 : V) where
  toRoot : L →+* RootExtension (G := G) v0
  r : L
  root_image : toRoot r =
    (twoLthRootAt (G := G) v0 : RootExtension (G := G) v0) ^ l.value
  phase : PhaseExponentData l

variable (I : P5NamedInputs (L := L) (l := l) (G := G) (v0 := v0))

/-- The bridge built from the named inputs, with canonical cOfPhase and
comparison_cOfPhase. -/
noncomputable def bridgeOfInputs :
    P5AnalyticRootBridge L (RootExtension (G := G) v0) l :=
  actualP5Bridge (G := G) (v0 := v0) I.toRoot I.r
    (cOfPhase (G := G) (v0 := v0) I.phase.m) I.phase.m I.root_image
    (comparison_cOfPhase (G := G) (v0 := v0) I.toRoot I.r I.root_image I.phase.m)

theorem p5_final_comparison
    (q i : L) (hr : I.r ^ 2 = q) (hr0 : I.r ≠ 0) (hi : i ^ 2 = -1)
    (hq : ‖q‖ < 1) (hTheta : oddTheta q i ≠ 0) (j : ThetaLabel (l := l)) :
    I.toRoot (oddTheta q (analyticThetaLabelPoint i I.r j) / oddTheta q i) =
      (cOfPhase (G := G) (v0 := v0) I.phase.m j : RootExtension (G := G) v0) *
        (paperPhaseUnit (G := G) (v0 := v0) I.phase.m j : RootExtension (G := G) v0) *
        (paperRootThetaUnit (G := G) (thetaLabelToSigned (l := l) j) v0 :
          RootExtension (G := G) v0) := by
  exact p5_bridge_compare (B := bridgeOfInputs (G := G) (v0 := v0) I)
    q i hr hr0 hi hq hTheta j

#print axioms p5_final_comparison

end LeanFormal.IUT.XiFPaper.Mzk1P5FinalSummaryActual
