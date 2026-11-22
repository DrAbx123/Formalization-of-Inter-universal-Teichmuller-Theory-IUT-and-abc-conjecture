/- R2 per-box bridge: paper Theta row volume V(p,j,t) <= collectionChoiceBound.

  `V(p,j,t)` is DEFINED as the paper Theta row normalized log volume: the
  degree-normalized Haar log-volume of the holomorphic hull of the possible images
  `arithmeticTupleHolomorphicHull places tuple e (arithmeticTupleStepVPossibleImages ...)`
  (a rootThetaRegion-type row box).  The DONE IUT IV Thm 1.10 Step (v) bound
  `FinitePlaceStepVAssembly.arithmeticTuple_stepV_hull_normalizedLogVolume_le_paperBound`
  gives
    V <= (-lambda + sum_i d_i + 1) * log p + sum_{i in exceptional} (3 + log e_i).
  This file supplies the exact arithmetic bridge from that paperBound shape to
  `collectionChoiceBound l logp iotaL j d oq et idag` (StepVProcessionAverage),
  under the paper identifications:
    * lambda >= (j^2/(2l)) * oq(et idag)  (slot coefficient is the q-order term),
    * sum_i d_i <= sum_i d (et i)         (different orders vs the d-vector of the row),
    * exceptional term <= 4(j+1) iotaL    (R4 exceptional slot bound,
                                           DONE `exceptionalSum_le_r4`).
  The remaining MISSING INSTANTIATION is the actual source family Phi_et / varpi
  (Ind1/Ind2 images at the row tuple) supplying the Step (v) hypotheses; no fake.
  No stub, no sorry/axiom. -/
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2R2PerRowBoundArithActual

/-- Arithmetic bridge: Step (v) paperBound <= collectionChoiceBound under the three
    paper identifications. -/
theorem paperBound_le_collectionChoiceBound
    (l logp iotaL lam dsum exc oqj dsum' : ℝ) (j : ℕ)
    (hlogp : 0 ≤ logp)
    (hlam : -lam ≤ -((j : ℝ) ^ 2 / (2 * l)) * oqj)
    (hD : dsum ≤ dsum')
    (hexc : exc ≤ 4 * ((j : ℝ) + 1) * iotaL) :
    (-lam + dsum + 1) * logp + exc ≤ (-((j : ℝ) ^ 2 / (2 * l) * oqj) + dsum' + 1) * logp + 4 * ((j : ℝ) + 1) * iotaL := by
  have h1 : -lam + dsum + 1 ≤ -((j : ℝ) ^ 2 / (2 * l) * oqj) + dsum' + 1 := by
    linarith
  have h2 := mul_le_mul_of_nonneg_right h1 hlogp
  linarith

/-- Row-volume form: if V is at most the Step (v) paperBound, it is at most the
    collectionChoiceBound shape (the actual V is the DONE hull log-volume). -/
theorem rowV_le_collectionChoiceBound
    (V l logp iotaL lam dsum exc oqj dsum' : ℝ) (j : ℕ)
    (hlogp : 0 ≤ logp)
    (hV : V ≤ (-lam + dsum + 1) * logp + exc)
    (hlam : -lam ≤ -((j : ℝ) ^ 2 / (2 * l)) * oqj)
    (hD : dsum ≤ dsum')
    (hexc : exc ≤ 4 * ((j : ℝ) + 1) * iotaL) :
    V ≤ (-((j : ℝ) ^ 2 / (2 * l) * oqj) + dsum' + 1) * logp + 4 * ((j : ℝ) + 1) * iotaL :=
  le_trans hV (paperBound_le_collectionChoiceBound l logp iotaL lam dsum exc oqj dsum' j
    hlogp hlam hD hexc)

#print axioms paperBound_le_collectionChoiceBound
#print axioms rowV_le_collectionChoiceBound

/-- **Equality form for the DONE bridge** `Mzk1BoxR2StepVBridgeActual.stepV_hull_le_collectionChoiceBound`:
    if the exact paper identifications `λ = (j^2/(2l)) oq(et idag)` and
    `exc = 4(j+1) iotaL` hold (the DONE bridge's `hparam`), then the paperBound is at most
    the collectionChoiceBound; the `d`-sum comparison is the only remaining inequality. -/
theorem paperBound_le_choice_of_paramEq
    (l logp iotaL lam dsum exc oqj dsum' : ℝ) (j : ℕ)
    (hlogp : 0 ≤ logp)
    (hlamEq : lam = ((j : ℝ) ^ 2 / (2 * l)) * oqj)
    (hexcEq : exc = 4 * ((j : ℝ) + 1) * iotaL)
    (hD : dsum ≤ dsum') :
    (-lam + dsum + 1) * logp + exc ≤ (-((j : ℝ) ^ 2 / (2 * l) * oqj) + dsum' + 1) * logp + 4 * ((j : ℝ) + 1) * iotaL := by
  subst hlamEq
  subst hexcEq
  have h1 : -(((j : ℝ) ^ 2 / (2 * l)) * oqj) + dsum + 1 ≤ -(((j : ℝ) ^ 2 / (2 * l)) * oqj) + dsum' + 1 := by
    linarith
  have h2 := mul_le_mul_of_nonneg_right h1 hlogp
  linarith

/-- **Exact mismatch/status**: the paper-to-Section-1 parameter equality
    `λ = (j^2/(2l)) oq(et idag)` is NOT proved from the current actual q-generator data;
    only the inequality `(j^2/(2l)) oq ≤ λ` is supplied by `lambdaFromQ_ge_slot`
    (R2PerRowSupplyActual).  The DONE bridge needs the equality as `hparam`. -/
def PaperStepVParamEqStatus : Prop :=
  True

#print axioms paperBound_le_choice_of_paramEq

end LeanFormal.IUT.XiFPaper.Mzk1G1F2R2PerRowBoundArithActual