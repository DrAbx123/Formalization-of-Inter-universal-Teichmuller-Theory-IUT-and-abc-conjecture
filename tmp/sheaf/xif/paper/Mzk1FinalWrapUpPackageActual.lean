/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCStage5AxiomGateActual
import tmp.sheaf.xif.paper.Mzk1ABCEntryQpilotActual
import tmp.sheaf.xif.paper.Mzk1ABCEntryGap2QpilotActual
import tmp.sheaf.xif.paper.Mzk1AcceptanceFinalRewriteActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalStatementActual
import Mathlib.Tactic

/-! # Mzk1FinalWrapUpPackageActual — final wrap-up package (qpilot lane)

A577 (qpilot lane, own name): one wrap-up file over green components:
* the Stage-5 gate evidence table (`stage5GateRows`, 8 rows) is re-exported;
* the conditional ABC entry (height bound, ABC conclusion);
* the Gap-2 named-estimate consumer;
* the paper target shape;
all as proved declarations. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalWrapUpPackageActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AxiomGateActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCEntryQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCEntryGap2QpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1AcceptanceFinalRewriteActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalStatementActual

/-- Wrap-up: the Stage-5 evidence table (8 rows). -/
def wrapUpGateRows : List (String × String × String) := stage5GateRows

theorem wrapUpGateRows_length : wrapUpGateRows.length = 8 :=
  stage5GateRows_length

/-- Wrap-up: the conditional ABC height bound. -/
theorem wrapUp_heightBound (D : Cor312ToABCBridgeInterface) :
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  abcEntry_heightBound D

/-- Wrap-up: the conditional ABC conclusion. -/
theorem wrapUp_abcConjecture (D : Cor312ToABCBridgeInterface) :
    ABCConjecture :=
  abcEntry_abcConjecture D

/-- Wrap-up: the Gap-2 region-volume bound. -/
theorem wrapUp_gap2 {X : Type} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (C.comparisonRegion a b c)).toReal ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D :=
  gap2_regionVolume_bound C

/-- Wrap-up: the paper target equivalence. -/
theorem wrapUp_paperTarget (qMag thetaMag : Real) :
    paperTarget qMag thetaMag ↔ thetaMag ≤ qMag :=
  acceptance_paperTarget_iff qMag thetaMag

#check wrapUp_heightBound
#check wrapUp_gap2
#check wrapUp_paperTarget

end LeanFormal.IUT.XiFPaper.Mzk1FinalWrapUpPackageActual
end
