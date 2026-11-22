/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FinalConditionalCertificateActual
import tmp.sheaf.xif.paper.Mzk1CorrectedGap1UnconditionalActual
import tmp.sheaf.xif.paper.Mzk1CorrectedGap2ToABCActual
import tmp.sheaf.xif.paper.Mzk1PaperRegionNecessityFinalActual
import tmp.sheaf.xif.paper.Mzk1GapTightnessActual

/-!
# A682 FINAL BOUNDARY CERTIFICATE V2 (mainline) — RETRACTED / VACUOUS

RETRACTED (A703 correction): components (b) 'corrected_gap1_unconditional' and
(c) 'correctedGap2_to_ABC' depend on the unsatisfiable 'hfull' hypothesis (see
'Mzk1FinalConditionalVacuityActual.hfull_unsatisfiable' and stage4
'Mzk1Stage4A703CorrectionActual.corrected_gap1_hypotheses_inconsistent'), so this
certificate is VACUOUS and must NOT be used as a conclusion.
Kept only as historical record.

# A682 FINAL BOUNDARY CERTIFICATE V2 (mainline) — original docstring (retracted)

(a) `final_3_12`; (b) corrected Gap 1 = THEOREM; (c) corrected Gap 2 shape => ABC;
(d) region-necessity audit; (e) bridge calibration; (f) scope: only remaining named
input is the corrected-region Gap 2 shape; ABC gate NOT passed; no canonical change.

Split into small helper theorems and a final conjunction to keep memory low. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingProductActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalCertificateActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap2ToABCActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperRegionNecessityFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1GapTightnessActual
open Mzk1LanaBridgeAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- The corrected-model Gap 2 shape (the only remaining named input). -/
def CorrectedGap2Shape
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
    (s1902LogVolume T
      (badInvScale T (eN aN bN cN) '' (s1902UnitRegion T ∪ {point aN bN cN}))).toReal ≤
        (1 + ε) * arithmeticWeight (abcRationalPoint aN cN) +
          (s1902LogVolume T (s1902Hull T)).toReal + D

def scopeRecordV2 : List (String × String) :=
  [ ("Cor 3.12 requirement chain", "PROVED_CHAIN (green)"),
    ("corrected-region Gap 1", "PROVED (full bad support, d_b >= 1, unit >= 0)"),
    ("corrected Gap 2 shape => ABC", "PROVED"),
    ("corrected-region Gap 2 shape", "NAMED (only remaining named input)"),
    ("Gap 2 shape <=> pure arithmetic BadSumWeightBound", "PROVED (correctedGap2_iff_arith)"),
    ("FinalNamedInput (explicit natRadical form of the Gap 2 shape)", "NAMED; see Mzk1BadSumWeightBoundExplicitActual.FinalNamedInput"),
    ("ABC => corrected Gap 2 (reverse)", "NOT_PROVED (not claimed); ABC gate NOT passed; no canonical change") ]

theorem scopeRecordV2_length : scopeRecordV2.length = 7 := rfl

theorem v2_final_3_12
    (hqneg : requirementSignedQ (rpRequirement T) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (rpRequirement T) hqneg ipl hipl she hshe apt hapt) :=
  final_3_12 (T := T) hqneg ipl hipl she hshe apt hapt

theorem v2_gap1
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hd : ∀ bBad : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ))
    (hfull : ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      aN + bN + cN + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN aN bN cN bBad))
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      Height.logHeight₁ (abcRationalPoint aN cN) ≤
        (1 + ε) * (s1902LogVolume T
          (badInvScale T (eN aN bN cN) ''
            (s1902UnitRegion T ∪ {point aN bN cN}))).toReal :=
  corrected_gap1_unconditional T point eN hc0 hcT hd hfull hunit ε hε

theorem v2_gap2
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hd : ∀ bBad : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ))
    (hfull : ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      aN + bN + cN + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN aN bN cN bBad))
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (hGap2 : CorrectedGap2Shape T point eN) : ABCConjecture :=
  correctedGap2_to_ABC T point eN hc0 hcT hd hfull hunit hGap2

theorem v2_region
    (point : Nat → Nat → Nat → S1902Carrier T) (ε : ℝ)
    {X : Type*} (W : IQHullLogVolumeInterface X)
    (region : Nat → Nat → Nat → Set X)
    (hfin : W.logVolume W.hull < ⊤)
    (hsub : ∀ a b c : Nat, IsABCTriple a b c → region a b c ⊆ W.hull) :
    PaperRegionNecessityFinalClaim T point ε W region hfin hsub :=
  paperRegionNecessityFinal T point ε W region hfin hsub

theorem v2_calibrated :
    Nonempty Cor312ToABCBridgeInterface.{0} ↔ ABCConjecture :=
  paperGap_boundary_calibrated

/-- **Final boundary certificate V2** as a conjunction of the green pieces. -/
theorem finalBoundaryCertificateV2
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hd : ∀ bBad : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ))
    (hfull : ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      aN + bN + cN + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN aN bN cN bBad))
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (hGap2 : CorrectedGap2Shape T point eN)
    (ε : ℝ) (hε : 0 < ε)
    (hqneg : requirementSignedQ (rpRequirement T) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt)
    {X : Type*} (W : IQHullLogVolumeInterface X)
    (region : Nat → Nat → Nat → Set X)
    (hfin : W.logVolume W.hull < ⊤)
    (hsub : ∀ a b c : Nat, IsABCTriple a b c → region a b c ⊆ W.hull) :
    (Cor312Conclusion
      (requirementContract (rpRequirement T) hqneg ipl hipl she hshe apt hapt)) ∧
      (∀ aN bN cN : Nat, IsABCTriple aN bN cN →
        Height.logHeight₁ (abcRationalPoint aN cN) ≤
          (1 + ε) * (s1902LogVolume T
            (badInvScale T (eN aN bN cN) ''
              (s1902UnitRegion T ∪ {point aN bN cN}))).toReal) ∧
      (ABCConjecture) ∧
      (PaperRegionNecessityFinalClaim T point ε W region hfin hsub) ∧
      (Nonempty Cor312ToABCBridgeInterface.{0} ↔ ABCConjecture) ∧
      (scopeRecordV2.length = 7) :=
  ⟨v2_final_3_12 T hqneg ipl hipl she hshe apt hapt,
   v2_gap1 T point eN hc0 hcT hd hfull hunit ε hε,
   v2_gap2 T point eN hc0 hcT hd hfull hunit hGap2,
   v2_region T point ε W region hfin hsub,
   v2_calibrated,
   scopeRecordV2_length⟩

end LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual.finalBoundaryCertificateV2