import tmp.sheaf.xif.paper.S1477OScalarBridgeActual
import tmp.sheaf.xif.paper.OrigXiFThetaLinkActual

-- S1496: concrete O scalar conditions toward OrigXiFThetaLinkActual.
-- If the actual C3 q has norm 1/5, the signed-hull scalar field holds.
-- Scalar_eq holds under the exact source-bad-q formula.  The concrete q
-- norm/order and the source-bad-q formula remain exact inputs; no fake
-- concrete Gaussian instance is asserted.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1496OScalarConcreteActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotScalarActual
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.XiFPaper.S1477OScalarBridgeActual
open LeanFormal.IUT.XiFPaper.OrigXiFThetaLinkActual

universe u uG uL uC

variable {X : Type u} [TopologicalSpace X] {l : PrimeGeFive}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}
variable (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
variable (D : OrigXiFPaperSignedHullData X l)
variable (C3 : SourcePilotRegionDataL I)

/-- Concrete q-norm condition: the actual C3 completion q has norm 1/5. -/
def S1496QNormOneFifth : Prop := ‖C3.q.q‖ = ((5 : Real)⁻¹)

/-- Exact source-bad-q formula for scalar_eq. -/
def S1496SourceBadQFormula : Prop :=
  -sourceBadQAbsLog I.initial = Real.log ‖C3.q.q‖

/-- q norm 1/5 gives the actual signed-hull comparison for every D. -/
theorem s1496SignedHull_of_qNorm_oneFifth
    (hq : S1496QNormOneFifth (I := I) C3) :
    OrigXiFOSignedHullExactField I D C3 := by
  apply origXiFOSignedHullExactField_of_one_le_qMagnitude I D C3
  rw [hq, Real.log_inv]
  have hlog5 : 1 ≤ Real.log (5 : Real) := by
    linarith [Real.log_five_gt_d9]
  linarith

/-- q norm 1/5 gives the paper qPilot scalar at most -1. -/
theorem s1496QPilotLogVolume_le_neg_one_of_qNorm_oneFifth
    (hq : S1496QNormOneFifth (I := I) C3) :
    OrigXiFPaperQPilotLogVolume C3 ≤ -1 := by
  rw [OrigXiFPaperQPilotLogVolume_eq_log_norm, hq, Real.log_inv]
  have hlog5 : 1 ≤ Real.log (5 : Real) := by
    linarith [Real.log_five_gt_d9]
  linarith

/-- Exact source-bad-q formula gives scalar_eq. -/
theorem s1496ScalarExact_of_sourceBadQFormula
    (h : S1496SourceBadQFormula (I := I) C3) :
    OrigXiFOScalarExactField I O C3 :=
  (origXiFOScalarExactField_iff_badQAbsLog I O C3).mpr h

/-- Conditional actual O-layer ThetaLink structure from the two concrete
scalar conditions. -/
noncomputable def s1496ThetaLinkActual
    (hq : S1496QNormOneFifth (I := I) C3)
    (hbad : S1496SourceBadQFormula (I := I) C3) :
    OrigXiFThetaLinkActual O D C3 :=
  origXiFThetaLinkActualOf O D C3
    (s1496ScalarExact_of_sourceBadQFormula O C3 hbad)
    (s1496SignedHull_of_qNorm_oneFifth D C3 hq)

/-- The concrete q-norm source field, retained exactly. -/
def S1496ConcreteQNormRequired : Prop := S1496QNormOneFifth (I := I) C3

/-- The concrete source-bad-q formula, retained exactly. -/
def S1496ConcreteSourceBadQRequired : Prop := S1496SourceBadQFormula (I := I) C3

#check S1496QNormOneFifth
#check s1496SignedHull_of_qNorm_oneFifth
#check s1496QPilotLogVolume_le_neg_one_of_qNorm_oneFifth
#check s1496ScalarExact_of_sourceBadQFormula
#check s1496ThetaLinkActual
#check S1496ConcreteQNormRequired
#check S1496ConcreteSourceBadQRequired

end LeanFormal.IUT.XiFPaper.S1496OScalarConcreteActual

end