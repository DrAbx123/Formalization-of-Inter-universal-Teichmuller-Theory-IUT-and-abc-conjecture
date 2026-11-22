import tmp.sheaf.xif.paper.Mzk1FinalBoundaryCertificateV2Actual
import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi final semantics consumer (A688)

Only proved directions: corrected Gap2 shape => ABC, and shape <=> BadSumWeightBound.
No ABC => Gap2 assertion. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIFinalSemanticsConsumerV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

theorem correctedGap2_shape_implies_ABC
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hd : ∀ bBad : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : Real))
    (hfull : ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      aN + bN + cN + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN aN bN cN bBad))
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (hGap2 : CorrectedGap2Shape T point eN) : ABCConjecture :=
  v2_gap2 T point eN hc0 hcT hd hfull hunit hGap2

theorem correctedGap2_arith_equiv
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hhull : 0 ≤ (s1902LogVolume T (s1902Hull T)).toReal) :
    CorrectedGap2Shape T point eN ↔ BadSumWeightBound T eN :=
  correctedGap2_iff_arith T point eN hc0 hcT hhull

#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual.v2_gap2
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual.correctedGap2_iff_arith

end LeanFormal.IUT.XiFPaper.Mzk1StepXIFinalSemanticsConsumerV2Actual

end
