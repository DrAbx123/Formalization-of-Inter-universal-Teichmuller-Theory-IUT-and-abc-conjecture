/- H-T 8.2 (second batch): the per-place conductor/different core and the discriminant tower
connection.  The conductor difference is bounded by the relative different term using the
local inequality delta >= e - 1 (supplied for p-adic places by
LeanFormal/IUT/Foundations/LocalFields/LocalDifferentUpperBound and Mzk1LpDifferentBoundActual). -/
import tmp.sheaf.xif.paper.Mzk1G1ConductorDifferentCancellationActual
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationCoreActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual

universe u

/-- Per-place data for the conductor/different comparison above one rational place:
e = e_{w/v}, f = f_{w/v}, logNv = log Nv, and differentExponent = delta_{w/v}. -/
structure LocalConductorDifferentData where
  W : Type u
  [fintypeW : Fintype W]
  /-- [L : Q] -/
  Ldim : ℕ
  Ldim_pos : 0 < Ldim
  /-- ramification indices e_{w/v} -/
  e : W → ℕ
  e_pos : ∀ w, 1 ≤ e w
  /-- residue degrees f_{w/v} -/
  f : W → ℕ
  /-- log Nv for the fixed K-place v -/
  logNv : W → ℝ
  logNv_nonneg : ∀ w, 0 ≤ logNv w
  /-- different exponents delta_{w/v} -/
  differentExponent : W → ℕ

attribute [instance] LocalConductorDifferentData.fintypeW

/-- The conductor-difference term (1/[L:Q]) * sum_w (e_{w/v} - 1) f_{w/v} log Nv. -/
def conductorDifference (D : LocalConductorDifferentData) : ℝ :=
  (1 / (D.Ldim : ℝ)) *
    ∑ w, (((D.e w : ℝ) - 1) * (D.f w : ℝ) * D.logNv w)

/-- The relative-different term (1/[L:Q]) * sum_w delta_{w/v} f_{w/v} log Nv. -/
def differentTerm (D : LocalConductorDifferentData) : ℝ :=
  (1 / (D.Ldim : ℝ)) *
    ∑ w, ((D.differentExponent w : ℝ) * (D.f w : ℝ) * D.logNv w)

/-- The conductor difference is bounded by the relative-different term, using
delta_{w/v} >= e_{w/v} - 1 (the local different bound). -/
theorem conductorDifference_le_differentTerm (D : LocalConductorDifferentData)
    (hdelta : ∀ w, D.e w - 1 ≤ D.differentExponent w) :
    conductorDifference D ≤ differentTerm D := by
  unfold conductorDifference differentTerm
  have hsum : ∑ w, (((D.e w : ℝ) - 1) * (D.f w : ℝ) * D.logNv w) ≤
      ∑ w, ((D.differentExponent w : ℝ) * (D.f w : ℝ) * D.logNv w) := by
    apply Finset.sum_le_sum
    intro w _
    have h1 : ((D.e w : ℝ) - 1) ≤ (D.differentExponent w : ℝ) := by
      have hcast : ((D.e w - 1 : ℕ) : ℝ) = (D.e w : ℝ) - 1 := by
        rw [Nat.cast_sub (D.e_pos w)]
        ring
      rw [← hcast]
      exact_mod_cast hdelta w
    have hf : (0 : ℝ) ≤ (D.f w : ℝ) := by positivity
    have hl : 0 ≤ D.logNv w := D.logNv_nonneg w
    have h2 := mul_le_mul_of_nonneg_right h1 hf
    have h3 := mul_le_mul_of_nonneg_right h2 hl
    simpa [mul_assoc] using h3
  have hcoef : (0 : ℝ) ≤ 1 / (D.Ldim : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left hsum hcoef

/-! ## Discriminant tower connection -/

/-- Log form of the discriminant tower formula:
log |disc L| = log |N(different(O_K,O_L))| + [L:K] log |disc K|. -/
theorem log_natAbs_discr_tower {K : Type u} [Field K] [NumberField K] {L : Type u} [Field L]
    [NumberField L] [Algebra K L] [Module.Finite (𝓞 K) (𝓞 L)] :
    Real.log ((discr L).natAbs : ℝ) =
      Real.log ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : ℝ) +
        (Module.finrank K L : ℝ) * Real.log ((discr K).natAbs : ℝ) := by
  have h := discriminant_tower_formula_ringOfIntegers (K := K) (L := L)
  have hcast : ((discr L).natAbs : ℝ) =
      ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : ℝ) *
        ((discr K).natAbs : ℝ) ^ Module.finrank K L := by
    rw [h]
    push_cast
    ring
  have hposAbs : (0 : ℝ) < ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : ℝ) := by
    have hnonzero : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) ≠ 0 := by
      intro h0
      exact differentIdeal_ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
    exact_mod_cast Nat.pos_of_ne_zero hnonzero
  have hposK : (0 : ℝ) < ((discr K).natAbs : ℝ) :=
    Nat.cast_pos.mpr (Int.natAbs_pos.mpr (discr_ne_zero K))
  have hmul : Real.log (((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : ℝ) *
      ((discr K).natAbs : ℝ) ^ Module.finrank K L) =
      Real.log ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : ℝ) +
        Real.log (((discr K).natAbs : ℝ) ^ Module.finrank K L) :=
    Real.log_mul hposAbs.ne' (pow_ne_zero _ hposK.ne')
  have hpow : Real.log (((discr K).natAbs : ℝ) ^ Module.finrank K L) =
      (Module.finrank K L : ℝ) * Real.log ((discr K).natAbs : ℝ) :=
    Real.log_pow _ _
  rw [hcast, hmul, hpow]

/-- The relative different log is the difference of the log discriminants:
log |N(different(O_K,O_L))| = log |disc L| - [L:K] log |disc K|. -/
theorem log_absNorm_differentIdeal_eq {K : Type u} [Field K] [NumberField K] {L : Type u}
    [Field L] [NumberField L] [Algebra K L] [Module.Finite (𝓞 K) (𝓞 L)] :
    Real.log ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : ℝ) =
      Real.log ((discr L).natAbs : ℝ) -
        (Module.finrank K L : ℝ) * Real.log ((discr K).natAbs : ℝ) := by
  have h := log_natAbs_discr_tower (K := K) (L := L)
  linarith

#print axioms conductorDifference_le_differentTerm
#print axioms log_natAbs_discr_tower
#print axioms log_absNorm_differentIdeal_eq
end LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationCoreActual
