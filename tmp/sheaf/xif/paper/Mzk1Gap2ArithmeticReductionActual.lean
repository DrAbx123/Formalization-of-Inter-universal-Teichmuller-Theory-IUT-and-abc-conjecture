/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CorrectedGap1UnconditionalActual
import tmp.sheaf.xif.paper.Mzk1CorrectedGap2ToABCActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-!
# A681 Gap 2 pure-arithmetic reduction (mainline)

On the corrected region the geometric object is eliminated:
* `correctedGap2_iff_arith`: the corrected-model Gap 2 shape is EQUIVALENT to the pure
  arithmetic inequality `Σ_b e_b d_b log p_b <= (1+ε) weight + D'`;
* `logN_le_log_c_add_log3`: `log N <= log c + log 3` on ABC triples;
* `correctedGap2_reduces_to_radical`: corrected Gap 2 implies the radical height bound
  `log c <= (1+ε) weight + D'` — i.e. the only remaining arithmetic content is the ABC
  radical inequality;
* the converse (ABC => corrected Gap 2) needs bad primes inside `rad(abc)` support and
  is NOT claimed.

No canonical change; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual

open scoped Pointwise ENNReal BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap2ToABCActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- The Gap 2 shape of the corrected model (local copy of `CorrectedGap2Shape`). -/
def CorrectedGap2Shape
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
    (s1902LogVolume T
      (badInvScale T (eN aN bN cN) '' (s1902UnitRegion T ∪ {point aN bN cN}))).toReal ≤
        (1 + ε) * arithmeticWeight (abcRationalPoint aN cN) +
          (s1902LogVolume T (s1902Hull T)).toReal + D
/-- The pure arithmetic inequality that the corrected-model Gap 2 is equivalent to. -/
def BadSumWeightBound
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
    (∑ bBad : Bad (nativePlaceSelection T),
      (eN aN bN cN bBad : ℝ) *
        ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) *
          Real.log ((qVFamTensorP T bBad : ℕ) : ℝ))) ≤
      (1 + ε) * arithmeticWeight (abcRationalPoint aN cN) + D

/-- **Gap 2 shape ⇔ pure arithmetic inequality** (geometry eliminated). -/
theorem correctedGap2_iff_arith
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hhull : 0 ≤ (s1902LogVolume T (s1902Hull T)).toReal) :
    CorrectedGap2Shape T point eN ↔ BadSumWeightBound T eN := by
  constructor
  · intro hGap2 ε hε
    obtain ⟨D, hD⟩ := hGap2 ε hε
    refine ⟨(s1902LogVolume T (s1902Hull T)).toReal + D, ?_⟩
    intro aN bN cN habc
    have hvol := correctedRegion_logLaw T point eN hc0 hcT aN bN cN
    have hD' := hD aN bN cN habc
    rw [hvol] at hD'
    have hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal := by
      rw [show s1902LogVolume T (s1902UnitRegion T) = 1 from s1902LogVolume_unitRegion T]
      norm_num
    linarith
  · intro harith ε hε
    obtain ⟨D, hD⟩ := harith ε hε
    refine ⟨(s1902LogVolume T (s1902UnitRegion T)).toReal + D, ?_⟩
    intro aN bN cN habc
    have hvol := correctedRegion_logLaw T point eN hc0 hcT aN bN cN
    have hD' := hD aN bN cN habc
    have hunit := hvol
    rw [hunit]
    linarith

/-- On ABC triples, `log N <= log c + log 3` (`N = a+b+c+1 = 2c+1 <= 3c`). -/
theorem logN_le_log_c_add_log3 {a b c : Nat} (habc : IsABCTriple a b c) :
    Real.log (((a + b + c + 1 : Nat)) : ℝ) ≤ Real.log (c : ℝ) + Real.log 3 := by
  have hstruct : 0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b := habc
  rcases hstruct with ⟨ha, hb, hsum, _⟩
  have hcpos : 0 < c := by omega
  have hNle : a + b + c + 1 ≤ 3 * c := by omega
  have hNpos : (0 : ℝ) < ((a + b + c + 1 : Nat) : ℝ) := by
    have : 0 < a + b + c + 1 := by omega
    exact_mod_cast this
  have h3cpos : (0 : ℝ) < 3 * (c : ℝ) := by positivity
  calc Real.log (((a + b + c + 1 : Nat)) : ℝ)
      ≤ Real.log (3 * (c : ℝ)) := by
        apply Real.log_le_log hNpos
        exact_mod_cast hNle
    _ = Real.log 3 + Real.log (c : ℝ) := by
        rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
          (by exact_mod_cast (ne_of_gt hcpos))]
    _ = Real.log (c : ℝ) + Real.log 3 := by ring

/-- **Reduction to the radical inequality**: corrected Gap 2 implies
  `log c <= (1+ε) weight + D'` (the ABC radical bound). -/
theorem correctedGap2_reduces_to_radical
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hd : ∀ bBad : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ))
    (hfull : ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      aN + bN + cN + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN aN bN cN bBad))
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (hGap2 : CorrectedGap2Shape T point eN) :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      Height.logHeight₁ (abcRationalPoint aN cN) ≤
        (1 + ε) * arithmeticWeight (abcRationalPoint aN cN) + D := by
  intro ε hε
  obtain ⟨D, hD⟩ := hGap2 ε hε
  refine ⟨(s1902LogVolume T (s1902Hull T)).toReal + D, ?_⟩
  intro aN bN cN habc
  have harith := log_height_le_badSum_of_fullSupport T eN hd aN bN cN habc
    (hfull aN bN cN habc)
  have hvol := correctedRegion_logLaw T point eN hc0 hcT aN bN cN
  have hD' := hD aN bN cN habc
  have hheight : Height.logHeight₁ (abcRationalPoint aN cN) = Real.log (cN : ℝ) :=
    abcRationalPoint_logHeight₁ habc
  rw [hheight]
  linarith

/-- Audit rows: the remaining arithmetic content. -/
def arithReductionRows : List (String × String) :=
  [ ("Gap 2 shape", "correctedRegionVol <= (1+ε) weight + hull + D"),
    ("geometry eliminated", "PROVED: iff pure arithmetic bad-sum bound"),
    ("bad-sum => radical bound", "PROVED: log c <= (1+ε) weight + D'"),
    ("converse", "NOT claimed: needs bad primes inside rad(abc) support"),
    ("scope", "ABC gate NOT passed; no canonical change") ]

theorem arithReductionRows_length : arithReductionRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual.correctedGap2_iff_arith
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual.logN_le_log_c_add_log3
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual.correctedGap2_reduces_to_radical