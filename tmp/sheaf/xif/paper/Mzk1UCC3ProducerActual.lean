import tmp.sheaf.xif.paper.Mzk1UCC3Actual
import LeanFormal.IUT.IUTIV.Estimates.Section2
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
open LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual
namespace LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual
variable {ι : Type*} [Fintype ι]
variable (w hullVol paper : ι → Real)
variable (hw : ∀ i, 0 ≤ w i)
variable (hpacket : ∀ i, hullVol i ≤ paper i)
/-- Weighted actual packet hull from pointwise StepV bounds. -/
noncomputable def ucWeightedHpkt : Real := ∑ i, w i * hullVol i
noncomputable def ucWeightedPaper : Real := ∑ i, w i * paper i
theorem ucWeightedHpkt_le_paper (hw : ∀ i, 0 ≤ w i)
    (hpacket : ∀ i, hullVol i ≤ paper i) :
    ucWeightedHpkt w hullVol ≤ ucWeightedPaper w paper := by
  unfold ucWeightedHpkt ucWeightedPaper
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpacket i) (hw i)
/-- C3 from the actual weighted packet hull and the paper coefficient identity. -/
theorem uc_c3_from_weighted
    {l A Q M : Real} (hHpkt : ucWeightedHpkt w hullVol ≤ ucWeightedPaper w paper)
    (hpaper : ucWeightedPaper w paper = kappa l * (A - cL l * Q) - M) :
    ucWeightedHpkt w hullVol ≤ kappa l * (A - cL l * Q) - M := by
  rw [← hpaper]
  exact hHpkt
#print axioms uc_c3_from_weighted

/-! ## 3. Binding the §5.4.4 prime-count input to Section2 -/

/-- Route §5.4.4 prime-count input: from the Section2 bound
pi(eta) <= 4 eta / (3 log eta) one gets pi(x) log x <= (4/3) E for every
1 <= x and eta_0 <= E.  This is the two-branch argument of route §5.4.4:
x >= eta_0 directly, and 1 <= x < eta_0 via pi(x) log x <= pi(eta_0) log(eta_0). -/
theorem primeCounting_mul_log_le_four_thirds
    {x E η₀ : ℝ} (hη : 0 < η₀)
    (hπ : ∀ η : ℝ, η₀ ≤ η →
      (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η))
    (hx : 1 ≤ x) (hE : η₀ ≤ E) (hxE : x ≤ E) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x ≤ (4 / 3) * E := by
  by_cases hxe : η₀ ≤ x
  · rcases eq_or_lt_of_le hx with hxone | hxone
    · subst hxone
      simp only [Nat.floor_one, Nat.primeCounting_one, Nat.cast_zero, zero_mul]
      nlinarith [hη]
    · have hlog : 0 < Real.log x := Real.log_pos hxone
      have h1 := hπ x hxe
      have h2 : (4 * x / (3 * Real.log x)) * Real.log x = 4 * x / 3 := by
        field_simp
      have hmul : (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x ≤ 4 * x / 3 := by
        calc (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x
            ≤ (4 * x / (3 * Real.log x)) * Real.log x :=
              mul_le_mul_of_nonneg_right h1 hlog.le
          _ = 4 * x / 3 := h2
      nlinarith
  · have hxle : x ≤ η₀ := le_of_not_ge hxe
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
    have hlogη : 0 ≤ Real.log η₀ := Real.log_nonneg (by linarith)
    have hlogpos : 0 < Real.log η₀ := Real.log_pos (by linarith)
    have hmonoπ : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (Nat.primeCounting ⌊η₀⌋₊ : ℝ) := by
      exact_mod_cast Nat.monotone_primeCounting (Nat.floor_le_floor hxle)
    have hmonolog : Real.log x ≤ Real.log η₀ := Real.log_le_log (by linarith) hxle
    have hπη : (Nat.primeCounting ⌊η₀⌋₊ : ℝ) * Real.log η₀ ≤ (4 / 3) * η₀ := by
      have h1 := hπ η₀ le_rfl
      have hmul : (4 * η₀ / (3 * Real.log η₀)) * Real.log η₀ = 4 * η₀ / 3 := by
        field_simp
      have h2 := mul_le_mul_of_nonneg_right h1 hlogpos.le
      rw [hmul] at h2
      linarith
    have hprod : (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x ≤
        (Nat.primeCounting ⌊η₀⌋₊ : ℝ) * Real.log η₀ :=
      mul_le_mul hmonoπ hmonolog hlogx (Nat.cast_nonneg _)
    have hE' : (4 / 3) * η₀ ≤ (4 / 3) * E := by nlinarith
    linarith

/-- The actual Section2 donor (IUT IV Prop 1.6, Section2.lean:409) instantiates
the route §5.4.4 prime-count input. -/
theorem exists_primeCounting_mul_log_le_four_thirds :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ x E : ℝ, 1 ≤ x → η₀ ≤ E → x ≤ E →
      (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x ≤ (4 / 3) * E := by
  obtain ⟨η₀, hη₀, hπ⟩ :=
    LeanFormal.IUT.IUTIV.Estimates.iutIVProp16_primeCounting_le_four_thirds_eventually
  exact ⟨η₀, hη₀, fun x E hx hE hxE => primeCounting_mul_log_le_four_thirds hη₀ hπ hx hE hxE⟩

#print axioms primeCounting_mul_log_le_four_thirds
#print axioms exists_primeCounting_mul_log_le_four_thirds

end LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual
end