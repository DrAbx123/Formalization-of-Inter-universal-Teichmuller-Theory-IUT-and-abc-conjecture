import tmp.sheaf.xif.paper.Mzk1DExactLowerActual
import Mathlib.Tactic

/-!
# A865 L7 proof: D_exact lower bound for the prime-conductor case (shehdd)

L7 target (`Mzk1DExactLowerActual.DExactLowerTarget`):
`(1 - 1/l)·log p ≤ D_exact`.

Paper normalization (Route C §2): `D_exact = log d + log f + arch` where
`d` is the discriminant/degree contribution (log d ≥ 0), `f` the Artin conductor
(prime conductor case: `f = p`, so `log f = log p`), and `arch` the archimedean
contribution (≥ 0).  The local normalization may put a weight
`(1 - 1/(e·l))` on the conductor term with `e ≥ 1` (local ramification index);
for `e = 1` this is exactly `(1 - 1/l)·log p`.

Proved here:
* `logp_nonneg` : `0 ≤ log p` for a prime conductor p;
* `L7_proved` : `log d ≥ 0`, `arch ≥ 0`, `l ≥ 1` ⇒ `DExactLowerTarget` for
  `DExactPrimeConductor = log d + log p + arch`;
* `L7_proved_normalized` : with the weight `(1 - 1/(e·l))`, `e ≥ 1`, `l ≥ 1`, the same
  lower bound holds; so the normalization can only increase the conductor coefficient.

So L7 is **directly provable** once `D_exact` is the paper-normalized
`log d + (weighted log f) + arch` expression; the only remaining obligation is to
identify the paper/normalization expression with this shape.

No RETRACTED statement.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1L7ProofActual

open LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual
open LeanFormal.IUT.XiFPaper.Mzk1KappaLemmaActual
open LeanFormal.IUT.XiFPaper.Mzk1SSIneqExplicitFormActual
open scoped BigOperators

/-- `log p ≥ 0` for a prime conductor. -/
theorem logp_nonneg (C : PrimeConductorCurve) :
    0 ≤ Real.log (C.p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (C.p : ℝ) := by exact_mod_cast C.hp.two_le
  exact Real.log_nonneg (by linarith)

/-- Prime-conductor paper-normalization shape: `D_exact = log d + log p + arch`, with
`d` the different/discriminant contribution and `arch` the archimedean term. -/
def DExactPrimeConductor (C : PrimeConductorCurve) (logd arch : ℝ) : ℝ :=
  logd + Real.log (C.p : ℝ) + arch

/-- Normalized shape: the conductor term carries the weight `(1 - 1/(e·l))`.
`e ≥ 1` is the local ramification index. -/
def DExactNormalized (C : PrimeConductorCurve) (logd arch e l : ℝ) : ℝ :=
  logd + (1 - 1 / (e * l)) * Real.log (C.p : ℝ) + arch

/-- Coefficient comparison: for `e ≥ 1`, `l ≥ 1`, `1 - 1/l ≤ 1 - 1/(e·l)`. -/
theorem one_sub_inv_le_normalized {e l : ℝ} (he : 1 ≤ e) (hl : 1 ≤ l) :
    1 - 1 / l ≤ 1 - 1 / (e * l) := by
  have hl0 : (0 : ℝ) < l := by linarith
  have he0 : (0 : ℝ) < e := by linarith
  have hden : (0 : ℝ) < e * l := mul_pos he0 hl0
  have hle : 1 / (e * l) ≤ 1 / l := by
    apply one_div_le_one_div_of_le hl0
    nlinarith
  linarith

/-- **L7 (prime-conductor, unweighted)**: if `log d ≥ 0`, `arch ≥ 0`, `l ≥ 1`, then
`(1 - 1/l)·log p ≤ log d + log p + arch`. -/
theorem L7_proved (C : PrimeConductorCurve) (l logd arch : ℝ)
    (hlogd : 0 ≤ logd) (harch : 0 ≤ arch) (hl1 : 1 ≤ l) :
    DExactLowerTarget C l (DExactPrimeConductor C logd arch) := by
  unfold DExactLowerTarget DExactPrimeConductor
  have hlogp := logp_nonneg C
  have hl0 : (0 : ℝ) < l := by linarith
  have hcoef : 1 - 1 / l ≤ 1 := by
    have : 0 ≤ 1 / l := one_div_nonneg.mpr (le_of_lt hl0)
    linarith
  have hmul : (1 - 1 / l) * Real.log (C.p : ℝ) ≤ Real.log (C.p : ℝ) :=
    by simpa [one_mul] using mul_le_mul_of_nonneg_right hcoef hlogp
  linarith

/-- **L7 (prime-conductor, weighted normalization)**: with weight
`(1 - 1/(e·l))`, `e ≥ 1`, `l ≥ 1`, `log d ≥ 0`, `arch ≥ 0`, the target still holds. -/
theorem L7_proved_normalized (C : PrimeConductorCurve) (l logd arch e : ℝ)
    (hlogd : 0 ≤ logd) (harch : 0 ≤ arch) (he : 1 ≤ e) (hl1 : 1 ≤ l) :
    DExactLowerTarget C l (DExactNormalized C logd arch e l) := by
  unfold DExactLowerTarget DExactNormalized
  have hlogp := logp_nonneg C
  have hcoef := one_sub_inv_le_normalized he hl1
  have hmul : (1 - 1 / l) * Real.log (C.p : ℝ) ≤
      (1 - 1 / (e * l)) * Real.log (C.p : ℝ) :=
    mul_le_mul_of_nonneg_right hcoef hlogp
  linarith

/-- Consumer: L7 in the unweighted normalization + Mestre–Oesterlé + Θ-data legality
⇒ `SSIneqExplicit` (conditional on the paper identification of `D_exact`). -/
theorem ssIneqExplicit_of_L7 (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (l : ℕ) (L : ThetaDataLegality C l) (logd arch : ℝ)
    (hlogd : 0 ≤ logd) (harch : 0 ≤ arch) :
    SSIneqExplicit (sL (l : ℝ))
      ((C.e : ℝ) * Real.log (C.p : ℝ)) (l : ℝ)
      ((((l : ℝ) + 5) / 4) * DExactPrimeConductor C logd arch) := by
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 11) L.l_ge_11)
  have hD : DExactLowerTarget C (l : ℝ) (DExactPrimeConductor C logd arch) :=
    L7_proved C (l : ℝ) logd arch hlogd harch hl1
  exact ssIneqExplicit_of_dExactLower hMO C l L (DExactPrimeConductor C logd arch) hD (logp_nonneg C)

structure L7Row where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def l7Rows : List L7Row :=
  [ ⟨"D_exact shape", "log d + log f + arch; prime conductor f=p; log d, arch >= 0", "PAPER_NORMALIZATION"⟩
  , ⟨"L7 unweighted", "(1-1/l)log p <= log d + log p + arch for l>=1", "PROVED (L7_proved)"⟩
  , ⟨"L7 weighted", "(1-1/(e l))log p weight, e>=1: coefficient >= (1-1/l)", "PROVED (L7_proved_normalized)"⟩
  , ⟨"log p nonneg", "p prime conductor", "PROVED (logp_nonneg)"⟩
  , ⟨"consumer", "L7 + Mestre-Oesterle + legality => SSIneqExplicit", "PROVED (ssIneqExplicit_of_L7)"⟩
  , ⟨"remaining identification", "paper/normalization expression must equal log d + weighted log f + arch", "PENDING (source bridge)"⟩
  , ⟨"scope", "no fake D_exact; no sorry/axiom; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem l7Rows_length : l7Rows.length = 7 := rfl

theorem l7Rows_has_pending :
    l7Rows.any (fun r => r.status = "PENDING (source bridge)") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1L7ProofActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1L7ProofActual.L7_proved
#print axioms LeanFormal.IUT.XiFPaper.Mzk1L7ProofActual.L7_proved_normalized
#print axioms LeanFormal.IUT.XiFPaper.Mzk1L7ProofActual.ssIneqExplicit_of_L7
