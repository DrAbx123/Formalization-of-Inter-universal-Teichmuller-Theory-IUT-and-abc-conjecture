import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage
import Mathlib.Tactic
/-!
# R2 inequality bridge: paper StepV bound ⇒ `collectionChoiceBound`

No equality/param identification is used (per Lead ruling).  With
`paperBound = (-λ + dsum + 1) logp + exc` and
`collectionChoiceBound = (-(j²/(2l)) oq(et idag) + ∑ d(et i) + 1) logp + 4(j+1) iotaL`,
the inequalities `slot := (j²/(2l)) oq(et idag) ≤ λ`, `dsum ≤ ∑ d(et i)`,
`exc ≤ 4(j+1) iotaL`, and `logp ≥ 0` give `paperBound ≤ collectionChoiceBound`.
Composition with `V ≤ paperBound` (`Mzk1BoxReadoutLocalActual.packetHull_normalizedLogVolume_le_box`)
yields the actual per-box upper `V ≤ collectionChoiceBound`.
-/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1BoxR2InequalityBridgeActual
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
universe u

theorem paperBound_le_collectionChoiceBound {E : Type u} [Fintype E]
    (l logp iotaL : ℝ) (j : ℕ) (d oq : E → ℝ) (et : Fin (j + 1) → E)
    (idag : Fin (j + 1)) (lam dsum exc : ℝ)
    (hslot : (j : ℝ) ^ 2 / (2 * l) * oq (et idag) ≤ lam)
    (hd : dsum ≤ ∑ i, d (et i))
    (hexc : exc ≤ 4 * ((j : ℝ) + 1) * iotaL)
    (hlogp : 0 ≤ logp) :
    (-lam + dsum + 1) * logp + exc ≤ collectionChoiceBound l logp iotaL j d oq et idag := by
  unfold LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionChoiceBound
  have h1 : (-lam) * logp ≤ (-((j : ℝ) ^ 2 / (2 * l) * oq (et idag))) * logp :=
    mul_le_mul_of_nonneg_right (by linarith [hslot]) hlogp
  have h2 : dsum * logp ≤ (∑ i, d (et i)) * logp :=
    mul_le_mul_of_nonneg_right hd hlogp
  nlinarith [h1, h2, hexc]

theorem packetHull_le_collectionChoiceBound {E : Type u} [Fintype E]
    (l logp iotaL : ℝ) (j : ℕ) (d oq : E → ℝ) (et : Fin (j + 1) → E)
    (idag : Fin (j + 1)) (V lam dsum exc : ℝ)
    (hV : V ≤ (-lam + dsum + 1) * logp + exc)
    (hslot : (j : ℝ) ^ 2 / (2 * l) * oq (et idag) ≤ lam)
    (hd : dsum ≤ ∑ i, d (et i))
    (hexc : exc ≤ 4 * ((j : ℝ) + 1) * iotaL)
    (hlogp : 0 ≤ logp) :
    V ≤ collectionChoiceBound l logp iotaL j d oq et idag :=
  le_trans hV (by
    unfold LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionChoiceBound
    have h1 : (-lam) * logp ≤ (-((j : ℝ) ^ 2 / (2 * l) * oq (et idag))) * logp :=
      mul_le_mul_of_nonneg_right (by linarith [hslot]) hlogp
    have h2 : dsum * logp ≤ (∑ i, d (et i)) * logp :=
      mul_le_mul_of_nonneg_right hd hlogp
    nlinarith [h1, h2, hexc])

#print axioms paperBound_le_collectionChoiceBound
#print axioms packetHull_le_collectionChoiceBound
end LeanFormal.IUT.XiFPaper.Mzk1BoxR2InequalityBridgeActual
end