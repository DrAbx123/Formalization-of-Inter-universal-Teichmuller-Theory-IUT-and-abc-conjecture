/- Route 8.5 F7, p | n case: arithmetic adapter.  If the local different exponent delta is
bounded by e * (v_p(e) + 1) (the LocalDifferentUpperBound shape), then the normalized
contribution of that prime is at most (v_p(e) + 1) * log p, which depends only on p and n. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F7PvdnAdapterActual

/-- The normalized different contribution of a prime with delta <= e*(v_p(e)+1) is bounded by
(v_p(e)+1)*log p. -/
theorem normalizedDifferentContribution_le {p : Nat} [Fact p.Prime] {e δ : Nat} (he : 0 < e)
    (hδ : δ ≤ e * (padicValNat p e + 1)) :
    (δ : ℝ) * Real.log (p : ℝ) / (e : ℝ) ≤
      ((padicValNat p e + 1 : Nat) : ℝ) * Real.log (p : ℝ) := by
  have hp0 : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  rw [div_le_iff₀ heR]
  have hδR : (δ : ℝ) ≤ (e : ℝ) * ((padicValNat p e + 1 : Nat) : ℝ) := by
    exact_mod_cast hδ
  have hmul : (δ : ℝ) * Real.log (p : ℝ) ≤
      ((e : ℝ) * ((padicValNat p e + 1 : Nat) : ℝ)) * Real.log (p : ℝ) :=
    mul_le_mul_of_nonneg_right hδR hp0
  calc (δ : ℝ) * Real.log (p : ℝ)
      ≤ ((e : ℝ) * ((padicValNat p e + 1 : Nat) : ℝ)) * Real.log (p : ℝ) := hmul
    _ = (((padicValNat p e + 1 : Nat) : ℝ) * Real.log (p : ℝ)) * (e : ℝ) := by ring

/-- The same bound as a finite sum over a set of local places: with Ldim >= sum of e_i, the
total normalized contribution is bounded by the fixed constant (v_p(e)+1)*log p * Ldim/Ldim
in the aggregated form used by route F7. -/
theorem sum_normalizedDifferentContribution_le {ι : Type*} [Fintype ι] {p : Nat} [Fact p.Prime]
    {e δ : ι → Nat} {Ldim : Nat} (hL : 0 < Ldim)
    (he : ∀ i, 0 < e i) (hδ : ∀ i, δ i ≤ e i * (padicValNat p (e i) + 1))
    (hLdim : ((∑ i, e i) : ℝ) ≤ (Ldim : ℝ)) :
    (∑ i, (δ i : ℝ) * Real.log (p : ℝ)) / (Ldim : ℝ) ≤
      ((∑ i, ((padicValNat p (e i) + 1 : Nat) : ℝ) * (e i : ℝ)) * Real.log (p : ℝ)) /
        (Ldim : ℝ) := by
  have hp0 : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  have hsum_le : (∑ i, (δ i : ℝ) * Real.log (p : ℝ)) ≤
      ∑ i, (((padicValNat p (e i) + 1 : Nat) : ℝ) * (e i : ℝ)) * Real.log (p : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    have hδi : (δ i : ℝ) ≤ (e i : ℝ) * ((padicValNat p (e i) + 1 : Nat) : ℝ) := by
      exact_mod_cast hδ i
    have hmul := mul_le_mul_of_nonneg_right hδi hp0
    calc (δ i : ℝ) * Real.log (p : ℝ)
        ≤ ((e i : ℝ) * ((padicValNat p (e i) + 1 : Nat) : ℝ)) * Real.log (p : ℝ) := hmul
      _ = (((padicValNat p (e i) + 1 : Nat) : ℝ) * (e i : ℝ)) * Real.log (p : ℝ) := by ring
  have hLdimR : (0 : ℝ) < (Ldim : ℝ) := by exact_mod_cast hL
  have hsum_log : (∑ i, (((padicValNat p (e i) + 1 : Nat) : ℝ) * (e i : ℝ)) * Real.log (p : ℝ)) =
      (∑ i, ((padicValNat p (e i) + 1 : Nat) : ℝ) * (e i : ℝ)) * Real.log (p : ℝ) := by
    rw [Finset.sum_mul]
  rw [hsum_log] at hsum_le
  exact div_le_div_of_nonneg_right hsum_le (le_of_lt hLdimR)

#print axioms normalizedDifferentContribution_le
#print axioms sum_normalizedDifferentContribution_le
end LeanFormal.IUT.XiFPaper.Mzk1G1F7PvdnAdapterActual
