/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FinalBoundaryCertificateV2Actual
import tmp.sheaf.xif.paper.Mzk1BadSumWeightBoundExplicitActual
import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import tmp.sheaf.xif.paper.Mzk1CorrectedGap2ToABCActual

/-!
# A694 FINAL CONDITIONAL ABC (mainline) — RETRACTED / VACUOUS

RETRACTED (A703 correction): the hypothesis 'hfull' of 'final_conditional_ABC'
(for fixed T, the bad-prime support of N = a+b+c+1) is UNSATISFIABLE —
machine-checked in 'Mzk1FinalConditionalVacuityActual.hfull_unsatisfiable'.
Hence 'final_conditional_ABC' and 'final_theorem_package' below are VACUOUS and
must NOT be used as conclusions.  The N = a+b+c+1 scaling is not the paper
structure (paper: bad primes = primes of abc; weights normalized by [F_v:Q_p]/[F:Q]).
Kept only as historical record.

# A694 FINAL CONDITIONAL ABC (mainline) — original docstring (retracted)

`final_conditional_ABC`: the single explicit arithmetic input `NatRadicalWeightBound`
(= `FinalNamedInput` = explicit natRadical bad-sum inequality) implies `ABCConjecture`,
through `BadSumWeightBound` -> `CorrectedGap2Shape` -> `correctedGap2_to_ABC`.

`final_theorem_package`: (a) `final_3_12`; (b) `NatRadicalWeightBound -> ABCConjecture`;
(c) scope record: the reverse is NOT proved/asserted; ABC gate NOT passed; no canonical
change.  This is the final delivery: everything in IUT 3.12 -> ABC is machine-checked
except the single explicit arithmetic hypothesis `NatRadicalWeightBound`.

Does not import the retired MachineProof file. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 600000

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalABCActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingProductActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalCertificateActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap2ToABCActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual
open LeanFormal.IUT.XiFPaper.Mzk1BadSumWeightBoundExplicitActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- **The single explicit arithmetic hypothesis** (natRadical bad-sum form). -/
def NatRadicalWeightBound
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) : Prop :=
  Mzk1BadSumWeightBoundExplicitActual.FinalNamedInput T eN

/-- **Final conditional ABC**: `NatRadicalWeightBound` implies `ABCConjecture`. -/
theorem final_conditional_ABC
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hd : ∀ bBad : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ))
    (hfull : ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      aN + bN + cN + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN aN bN cN bBad))
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (hhull : 0 ≤ (s1902LogVolume T (s1902Hull T)).toReal)
    (hnat : NatRadicalWeightBound T eN) : ABCConjecture := by
  have hbad : Mzk1Gap2ArithmeticReductionActual.BadSumWeightBound T eN :=
    (Mzk1BadSumWeightBoundExplicitActual.badSumWeightBound_iff_nat T eN).mpr hnat
  have hshape : Mzk1Gap2ArithmeticReductionActual.CorrectedGap2Shape T point eN :=
    (Mzk1Gap2ArithmeticReductionActual.correctedGap2_iff_arith T point eN hc0 hcT hhull).mpr hbad
  have hshapeV2 : Mzk1FinalBoundaryCertificateV2Actual.CorrectedGap2Shape T point eN := by
    simpa only [Mzk1Gap2ArithmeticReductionActual.CorrectedGap2Shape,
      Mzk1FinalBoundaryCertificateV2Actual.CorrectedGap2Shape] using hshape
  exact Mzk1CorrectedGap2ToABCActual.correctedGap2_to_ABC T point eN hc0 hcT hd hfull hunit hshapeV2

/-- Scope record of the final delivery. -/
def scopeRecordFinal : List (String × String) :=
  [ ("IUT 3.12 requirement chain", "PROVED_CHAIN (green)"),
    ("ABC from NatRadicalWeightBound", "PROVED (final_conditional_ABC)"),
    ("reverse / ABC gate", "NOT_PROVED; ABC gate NOT passed; no canonical change") ]

theorem scopeRecordFinal_length : scopeRecordFinal.length = 3 := rfl

/-- **Final theorem package**: 3.12 chain, conditional ABC, and scope. -/
theorem final_theorem_package
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hd : ∀ bBad : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ))
    (hfull : ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      aN + bN + cN + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN aN bN cN bBad))
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (hhull : 0 ≤ (s1902LogVolume T (s1902Hull T)).toReal)
    (hqneg : requirementSignedQ (rpRequirement T) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    (Cor312Conclusion
      (requirementContract (rpRequirement T) hqneg ipl hipl she hshe apt hapt)) ∧
      (NatRadicalWeightBound T eN → ABCConjecture) ∧
      (scopeRecordFinal.length = 3) :=
  ⟨final_3_12 (T := T) hqneg ipl hipl she hshe apt hapt,
   fun hnat => final_conditional_ABC T point eN hc0 hcT hd hfull hunit hhull hnat,
   scopeRecordFinal_length⟩

end LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalABCActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalABCActual.final_conditional_ABC
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalABCActual.final_theorem_package