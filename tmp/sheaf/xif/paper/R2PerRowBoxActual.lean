/- R2 per-row box (route §4.1 / IV L1691-1696): B_j(t,s) = (-λ_s + dsum + 1)·logp + exc,
and the exceptional bound `exc ≤ 4(j+1)·ι·log(e*_mod·l)` from the StepV donor.

Reuse: LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage.{collectionChoiceBound,
exceptionalSum_le_r4}.  Inequalities only; no equalities are assumed as source data.
-/
import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.R2PerRowBoxActual
open LeanFormal.IUT.IUTIV.StepVProcessionAverage

variable {E : Type*} [Fintype E]

/-- Per-row box `B_j(t,s) = (-λ_s + dsum + 1)·logp + exc` (IV L1691-1696). -/
def perRowBox (lam dsum exc logp : ℝ) : ℝ := (-lam + dsum + 1) * logp + exc

/-- Per-row bound: `slot := (j²/(2l))·oq(t s) ≤ λ`, `dsum ≤ Σ_i d(t i)`,
`exc ≤ 4(j+1)·iota`, `0 ≤ logp`  =>  `B_j(t,s) ≤ collectionChoiceBound`. -/
theorem perRowBox_le_collectionChoiceBound
    (l logp iotaL : ℝ) (j : ℕ) (d oq : E → ℝ) (et : Fin (j + 1) → E)
    (idag : Fin (j + 1)) (lam dsum exc : ℝ)
    (hslot : (j : ℝ) ^ 2 / (2 * l) * oq (et idag) ≤ lam)
    (hd : dsum ≤ ∑ i, d (et i))
    (hexc : exc ≤ 4 * ((j : ℝ) + 1) * iotaL)
    (hlogp : 0 ≤ logp) :
    perRowBox lam dsum exc logp ≤ collectionChoiceBound l logp iotaL j d oq et idag := by
  unfold perRowBox collectionChoiceBound
  have h1 : -lam * logp ≤ -((j : ℝ) ^ 2 / (2 * l) * oq (et idag)) * logp := by
    nlinarith [hslot, hlogp]
  have h2 : dsum * logp ≤ (∑ i, d (et i)) * logp := by
    exact mul_le_mul_of_nonneg_right hd hlogp
  nlinarith [h1, h2, hexc]

/-- Exceptional bound from the StepV (R4) donor: for `Istar ⊆ I` with `I.card = j+1`,
`Σ_{i∈Istar} (3 + log e_i) ≤ 4(j+1)·(if p ≤ el then log el else 0)`. -/
theorem exceptional_bound_of_r4
    {α : Type*} (j : ℕ) (I Istar : Finset α) (hsub : Istar ⊆ I)
    (e : α → ℝ) (p el : ℝ) (hel : 1 ≤ el) (hcard : I.card = j + 1)
    (hR4 : ∀ i ∈ Istar, p ≤ el ∧ Real.log (e i) ≤ -3 + 4 * Real.log el) :
    (∑ i ∈ Istar, (3 + Real.log (e i))) ≤
      4 * ((j : ℝ) + 1) * (if p ≤ el then Real.log el else 0) := by
  have h := exceptionalSum_le_r4 I Istar hsub e p el hel hR4
  rw [hcard] at h
  push_cast at h
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

/-- Combined per-row bound with the exceptional bound discharged by the R4 donor. -/
theorem perRowBox_le_collectionChoiceBound_of_r4
    (l logp : ℝ) (j : ℕ) (d oq : E → ℝ) (et : Fin (j + 1) → E)
    (idag : Fin (j + 1)) (lam dsum : ℝ) {α : Type*} (I Istar : Finset α)
    (hsub : Istar ⊆ I) (e : α → ℝ) (p el : ℝ) (hel : 1 ≤ el) (hcard : I.card = j + 1)
    (hR4 : ∀ i ∈ Istar, p ≤ el ∧ Real.log (e i) ≤ -3 + 4 * Real.log el)
    (hslot : (j : ℝ) ^ 2 / (2 * l) * oq (et idag) ≤ lam)
    (hd : dsum ≤ ∑ i, d (et i)) (hlogp : 0 ≤ logp) :
    perRowBox lam dsum (∑ i ∈ Istar, (3 + Real.log (e i))) logp ≤ collectionChoiceBound l logp
      (if p ≤ el then Real.log el else 0) j d oq et idag :=
  perRowBox_le_collectionChoiceBound l logp (if p ≤ el then Real.log el else 0) j d oq et idag
    lam dsum (∑ i ∈ Istar, (3 + Real.log (e i))) hslot hd
    (exceptional_bound_of_r4 j I Istar hsub e p el hel hcard hR4) hlogp

#print axioms perRowBox_le_collectionChoiceBound
#print axioms exceptional_bound_of_r4
#print axioms perRowBox_le_collectionChoiceBound_of_r4
end LeanFormal.IUT.XiFPaper.R2PerRowBoxActual
end
