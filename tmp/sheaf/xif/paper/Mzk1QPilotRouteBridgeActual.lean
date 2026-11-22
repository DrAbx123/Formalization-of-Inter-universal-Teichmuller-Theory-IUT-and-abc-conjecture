/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1QPilotRouteActual
import tmp.sheaf.xif.paper.Mzk1CorrectedGap1UnconditionalActual
import tmp.sheaf.xif.paper.Mzk1CorrectedRegionLogLawProvedActual
import tmp.sheaf.xif.paper.Mzk1BadSumWeightBoundExplicitActual
import tmp.sheaf.xif.paper.Mzk1FinalConditionalABCActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-!
# A701 q-pilot route bridge: nonemptiness + equivalence with N-scaling (mainline)

* `QPilotScaleDataOn region`: q-pilot data on an arbitrary explicit region;
* `correctedQPilotData`: an ACTUAL instance built from the green corrected-region log
  law (`s = Σ_b e_b d_b log p_b`, region = `badInvScale eN '' unitRegion`), with
  `height_bound` from the green arithmetic core and `unit_nonneg` from the hypothesis;
* `gap1_of_qPilotRouteOn`: generic Gap 1 from q-pilot data;
* `qPilotRadicalBoundOn_implies_ABC`;
* `correctedQPilot_bound_iff_natRadicalWeightBound`: in this instance the q-pilot
  remaining input is the same as `NatRadicalWeightBound` (same ABC strength).

No canonical change; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotRouteBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogLawProvedActual
open LeanFormal.IUT.XiFPaper.Mzk1BadSumWeightBoundExplicitActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalABCActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- q-pilot scale data on an explicit region function. -/
structure QPilotScaleDataOn
    (region : Nat → Nat → Nat → Set (S1902Carrier T)) where
  s : Nat → Nat → Nat → ℝ
  h_nonneg : ∀ a b c : Nat, 0 ≤ s a b c
  height_bound : ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤ s a b c
  region_logLaw : ∀ a b c : Nat,
    (s1902LogVolume T (region a b c)).toReal =
      (s1902LogVolume T (s1902UnitRegion T)).toReal + s a b c
  unit_nonneg : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal

/-- Generic Gap 1 from q-pilot data. -/
theorem gap1_of_qPilotRouteOn
    (region : Nat → Nat → Nat → Set (S1902Carrier T))
    (D : QPilotScaleDataOn T region) (ε : ℝ) (hε : 0 < ε) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε) * (s1902LogVolume T (region a b c)).toReal := by
  intro a b c habc
  have hheight := D.height_bound a b c habc
  have hvol := D.region_logLaw a b c
  have hnonneg : 0 ≤ (s1902LogVolume T (region a b c)).toReal := by
    rw [hvol]; linarith [D.unit_nonneg, D.h_nonneg a b c]
  have hle1 : (1 : ℝ) ≤ 1 + ε := by linarith
  calc Height.logHeight₁ (abcRationalPoint a c) ≤ D.s a b c := hheight
    _ ≤ (s1902LogVolume T (region a b c)).toReal := by
        rw [hvol]; linarith [D.unit_nonneg]
    _ ≤ (1 + ε) * (s1902LogVolume T (region a b c)).toReal := by
        calc (s1902LogVolume T (region a b c)).toReal
            = 1 * (s1902LogVolume T (region a b c)).toReal := by ring
          _ ≤ (1 + ε) * (s1902LogVolume T (region a b c)).toReal := by
              exact mul_le_mul_of_nonneg_right hle1 hnonneg

/-- The remaining named input in q-pilot form on a region. -/
def qPilotRadicalBoundOn
    (region : Nat → Nat → Nat → Set (S1902Carrier T))
    (D : QPilotScaleDataOn T region) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ D0 : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
    D.s a b c ≤ (1 + ε) * arithmeticWeight (abcRationalPoint a c) + D0

theorem qPilotRadicalBoundOn_implies_ABC
    (region : Nat → Nat → Nat → Set (S1902Carrier T))
    (D : QPilotScaleDataOn T region)
    (hbound : qPilotRadicalBoundOn T region D) : ABCConjecture := by
  refine abcConjecture_iff_abcArithmeticWeightHeightBound.mpr ?_
  intro ε hε
  obtain ⟨D0, hD0⟩ := hbound ε hε
  refine ⟨D0, ?_⟩
  intro a b c habc
  have hh := D.height_bound a b c habc
  have hD' := hD0 a b c habc
  linarith

/-- **An ACTUAL q-pilot instance** built from the green corrected-region log law. -/
noncomputable def correctedQPilotData
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hd : ∀ bBad : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ))
    (hfull : ∀ a b c : Nat, IsABCTriple a b c →
      a + b + c + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN a b c bBad))
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal) :
    QPilotScaleDataOn T
      (fun a b c => badInvScale T (eN a b c) '' s1902UnitRegion T) where
  s := fun a b c => ∑ bBad : Bad (nativePlaceSelection T),
    (eN a b c bBad : ℝ) *
      ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) *
        Real.log ((qVFamTensorP T bBad : ℕ) : ℝ))
  h_nonneg := by
    intro a b c
    refine Finset.sum_nonneg ?_
    intro bBad _
    have hdb := hd bBad
    have hlogb : 0 ≤ Real.log ((qVFamTensorP T bBad : ℕ) : ℝ) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ ((qVFamTensorP T bBad : Nat) : ℝ) := by
        exact_mod_cast (le_of_lt (Fact.out : Nat.Prime (qVFamTensorP T bBad)).one_lt)
      simpa using this
    have he : (0 : ℝ) ≤ (eN a b c bBad : ℝ) := by positivity
    exact mul_nonneg he (mul_nonneg (by linarith) hlogb)
  height_bound := by
    intro a b c habc
    rw [abcRationalPoint_logHeight₁ habc]
    exact log_height_le_badSum_of_fullSupport T eN hd a b c habc (hfull a b c habc)
  region_logLaw := by
    intro a b c
    exact corrected_unitRegion_logLaw T (eN a b c) hc0 hcT
  unit_nonneg := hunit

/-- The instance's q-pilot remaining input is `NatRadicalWeightBound` (same strength). -/
theorem correctedQPilot_bound_iff_natRadicalWeightBound
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hd : ∀ bBad : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ))
    (hfull : ∀ a b c : Nat, IsABCTriple a b c →
      a + b + c + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN a b c bBad))
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal) :
    qPilotRadicalBoundOn T
        (fun a b c => badInvScale T (eN a b c) '' s1902UnitRegion T)
        (correctedQPilotData T eN hc0 hcT hd hfull hunit) ↔
      NatRadicalWeightBound T eN := by
  constructor
  · intro h ε hε
    obtain ⟨D0, hD0⟩ := h ε hε
    refine ⟨D0, ?_⟩
    intro a b c habc
    have hD' := hD0 a b c habc
    rw [arithmeticWeight_abc_eq_log_natRadical habc] at hD'
    exact hD'
  · intro h ε hε
    obtain ⟨D0, hD0⟩ := h ε hε
    refine ⟨D0, ?_⟩
    intro a b c habc
    have hD' := hD0 a b c habc
    rw [arithmeticWeight_abc_eq_log_natRadical habc]
    exact hD'

/-- Scope rows of the q-pilot/N-scaling cross calibration. -/
def bridgeRows : List (String × String) :=
  [ ("q-pilot data (region form)", "explicit structure QPilotScaleDataOn"),
    ("actual instance", "correctedQPilotData (green corrected-region log law)"),
    ("Gap 1 via q-pilot", "PROVED (gap1_of_qPilotRouteOn)"),
    ("q-pilot input <=> NatRadicalWeightBound", "PROVED (same ABC strength)"),
    ("scope", "routes equivalent; difficulty not removed; ABC gate NOT passed") ]

theorem bridgeRows_length : bridgeRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1QPilotRouteBridgeActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1QPilotRouteBridgeActual.correctedQPilot_bound_iff_natRadicalWeightBound
#print axioms LeanFormal.IUT.XiFPaper.Mzk1QPilotRouteBridgeActual.gap1_of_qPilotRouteOn
#print axioms LeanFormal.IUT.XiFPaper.Mzk1QPilotRouteBridgeActual.bridgeRows_length