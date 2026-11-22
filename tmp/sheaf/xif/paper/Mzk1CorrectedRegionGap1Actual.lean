/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CarrierBadInvScaleLawActual
import tmp.sheaf.xif.paper.Mzk1Gap1ScalingLawTargetActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# A665 Corrected comparison region and conditional Gap 1 (mainline)

Object-direction fix: the canonical `tripleScale` multiplies by `N`, which DECREASES the
p-adic Haar log-volume by `∑_b e_b d_b log p_b` (`e_b = v_{p_b}(N)`); the paper's region
is a λ-multiple (inverse powers of q), which INCREASES it.  Hence:

* `correctedRegion e := badInvScale e` (coordinatewise `(p_b^{e_b})⁻¹`);
* `correctedPaperRegion point a b c := correctedRegion e_N '' (unitRegion ∪ {point})`,
  `e_N b = v_{p_b}(a+b+c+1)`;
* **log-form hypothesis** (expected from the green
  `badInvScale_productHaar_pi`, rectangle case):
  `(s1902LogVolume correctedPaperRegion).toReal = unitReal + ∑ e_b d_b log p_b`
  — kept as an explicit hypothesis here, not assumed silently;
* **arithmetic core (PROVED)**: under full bad support `N = ∏ p_b^{e_b}` and `d_b ≥ 1`,
  `log c ≤ ∑ e_b d_b log p_b` (height is absorbed by the bad support);
* **conditional Gap 1 (PROVED)**: log-form hypothesis + arithmetic core + unit nonneg
  imply the Gap 1 height comparison;
* **boundary**: when the bad support is too small the sum is bounded, and the green
  `Mzk1CorrectedTripleScalingActual.corrected_gap1_fails_of_bounded_badPart` gives the
  large-triple counterexample (same object direction).

Nothing canonical changed; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionGap1Actual

open scoped Pointwise ENNReal
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleLawActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Corrected region: coordinatewise inverse bad-prime scaling with exponents `e`. -/
noncomputable def correctedRegion (e : Bad (nativePlaceSelection T) → Nat) :
    S1902Carrier T → S1902Carrier T :=
  badInvScale T e

/-- The corrected paper comparison region, using `e_b = v_{p_b}(a+b+c+1)`. -/
noncomputable def correctedPaperRegion
    (point : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat) : Set (S1902Carrier T) :=
  correctedRegion T (fun bBad => padicValNat (qVFamTensorP T bBad) (a + b + c + 1)) ''
    (s1902UnitRegion T ∪ {point a b c})

/-- **Log-form hypothesis** on the corrected region (expected from the green product
  Haar law; kept explicit). -/
def CorrectedRegionLogLaw (point : Nat → Nat → Nat → S1902Carrier T)
    (e : Bad (nativePlaceSelection T) → Nat) : Prop :=
  ∀ a b c : Nat,
    (s1902LogVolume T (correctedPaperRegion T point a b c)).toReal =
      (s1902LogVolume T (s1902UnitRegion T)).toReal +
        ∑ b : Bad (nativePlaceSelection T),
          (e b : ℝ) *
            ((Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : ℝ) *
              Real.log ((qVFamTensorP T b : ℝ)))

/-- **Arithmetic core (PROVED)**: full bad support and `d_b ≥ 1` make the bad-prime sum
  dominate the height: `log c ≤ ∑ e_b d_b log p_b`. -/
theorem log_height_le_badSum
    (point : Nat → Nat → Nat → S1902Carrier T)
    (e : Bad (nativePlaceSelection T) → Nat)
    (hd : ∀ b : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : ℝ))
    (a b c : Nat) (habc : IsABCTriple a b c)
    (hfull : a + b + c + 1 = ∏ b : Bad (nativePlaceSelection T),
      (qVFamTensorP T b) ^ (e b)) :
    Real.log (c : ℝ) ≤ ∑ b : Bad (nativePlaceSelection T),
      (e b : ℝ) *
        ((Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : ℝ) *
          Real.log ((qVFamTensorP T b : ℝ))) := by
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast habc.c_pos
  have hcle : (c : ℝ) ≤ ((a + b + c + 1 : Nat) : ℝ) := by
    have : c ≤ a + b + c + 1 := by omega
    exact_mod_cast this
  have hlogc : Real.log (c : ℝ) ≤ Real.log (((a + b + c + 1 : Nat)) : ℝ) :=
    Real.log_le_log hcpos hcle
  rw [hfull] at hlogc
  have hprodpos : (0 : ℝ) < ((∏ b : Bad (nativePlaceSelection T),
      (qVFamTensorP T b) ^ (e b) : Nat) : ℝ) := by
    have hposNat : 0 < ∏ b : Bad (nativePlaceSelection T), (qVFamTensorP T b) ^ (e b) := by
      apply Finset.prod_pos
      intro b _
      exact pow_pos (Fact.out : Nat.Prime (qVFamTensorP T b)).pos _
    exact_mod_cast hposNat
  have hlogprod : Real.log (((∏ b : Bad (nativePlaceSelection T),
      (qVFamTensorP T b) ^ (e b) : Nat) : ℝ)) =
      ∑ b : Bad (nativePlaceSelection T),
        (e b : ℝ) * Real.log ((qVFamTensorP T b : ℝ)) := by
    rw [Nat.cast_prod]
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl ?_
      intro b _
      rw [Nat.cast_pow, Real.log_pow]
    · intro b _
      have hp : (qVFamTensorP T b : Nat) ≠ 0 :=
        (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_zero
      exact_mod_cast (pow_ne_zero (e b) hp)
  rw [hlogprod] at hlogc
  have hlogp_nonneg : ∀ b : Bad (nativePlaceSelection T),
      0 ≤ Real.log ((qVFamTensorP T b : ℝ)) := by
    intro b
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ ((qVFamTensorP T b : Nat) : ℝ) := by
      exact_mod_cast (le_of_lt (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt)
    simpa using this
  have hsum_mono : (∑ b : Bad (nativePlaceSelection T),
        (e b : ℝ) * Real.log ((qVFamTensorP T b : ℝ))) ≤
      ∑ b : Bad (nativePlaceSelection T),
        (e b : ℝ) *
          ((Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : ℝ) *
            Real.log ((qVFamTensorP T b : ℝ))) := by
    refine Finset.sum_le_sum ?_
    intro b _
    have hdb := hd b
    have hlogb := hlogp_nonneg b
    have he_nonneg : (0 : ℝ) ≤ (e b : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hdb hlogb, he_nonneg, hlogb]
  linarith

/-- **Conditional Gap 1 for the corrected region (PROVED)**: log law + arithmetic
  core + unit nonneg give the Gap 1 height comparison. -/
theorem corrected_gap1_of_fullSupport
    (point : Nat → Nat → Nat → S1902Carrier T)
    (e : Bad (nativePlaceSelection T) → Nat)
    (hlog : CorrectedRegionLogLaw T point e)
    (hd : ∀ b : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : ℝ))
    (hfull : ∀ a b c : Nat, IsABCTriple a b c →
      a + b + c + 1 = ∏ b : Bad (nativePlaceSelection T), (qVFamTensorP T b) ^ (e b))
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε) * (s1902LogVolume T (correctedPaperRegion T point a b c)).toReal := by
  intro a b c habc
  have harith := log_height_le_badSum T point e hd a b c habc (hfull a b c habc)
  have hvol := hlog a b c
  have hpos : 0 ≤ (s1902LogVolume T (correctedPaperRegion T point a b c)).toReal := by
    rw [hvol]
    have hsum_nonneg : (0 : ℝ) ≤ ∑ b : Bad (nativePlaceSelection T),
        (e b : ℝ) *
          ((Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : ℝ) *
            Real.log ((qVFamTensorP T b : ℝ))) := by
      apply Finset.sum_nonneg
      intro b _
      have hlogb : 0 ≤ Real.log ((qVFamTensorP T b : ℝ)) := by
        apply Real.log_nonneg
        have : (1 : ℝ) ≤ ((qVFamTensorP T b : Nat) : ℝ) := by
          exact_mod_cast (le_of_lt (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt)
        simpa using this
      have hdb := hd b
      have he : (0 : ℝ) ≤ (e b : ℝ) := by positivity
      exact mul_nonneg he (mul_nonneg (by linarith) hlogb)
    linarith
  have hle1 : (1 : ℝ) ≤ 1 + ε := by linarith
  have hheight : Height.logHeight₁ (abcRationalPoint a c) = Real.log (c : ℝ) :=
    abcRationalPoint_logHeight₁ habc
  rw [hheight, hvol]
  have hsum_ge : Real.log (c : ℝ) ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal +
      ∑ b : Bad (nativePlaceSelection T),
        (e b : ℝ) *
          ((Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : ℝ) *
            Real.log ((qVFamTensorP T b : ℝ))) := by linarith
  have hX : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal +
      ∑ b : Bad (nativePlaceSelection T),
        (e b : ℝ) *
          ((Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : ℝ) *
            Real.log ((qVFamTensorP T b : ℝ))) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hle1 hX]

end LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionGap1Actual

end

