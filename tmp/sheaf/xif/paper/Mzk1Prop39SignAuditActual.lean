/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-!
# A529 Prop 3.9 sign audit: log-volume is INCREASING under inclusion; 3.12 is a
# containment statement, not a positive-magnitude inequality

Paper quotes (IUT III):
* Proposition 3.9, (i), lines 6858-6861: the local log-volumes are normalized so that
  the local holomorphic integral structure has log-volume 0, and 'multiplication of an
  element of M(-) by p_v corresponds to adding the quantity -log(p_v)'; i.e. the
  packet-normalization is **additive in the exponent** and log-volume = log of measure
  (up to the fixed normalization).
* Proposition 3.9, (i), lines 6888-6893: procession-normalization = 'taking the
  average, over the various capsules under consideration'.
* Cor 3.12 proof (xi-d), lines 10843-10849: define
    R_{<= -|log(Theta)|} := {lambda in R | lambda <= -|log(Theta)|}
  and state that `-|log(Theta)|` is the (negative) log-volume of `1,oU`, while
  `-|log(q)|` is the log-volume of the region arising from the representation of the
  q-pilot object on `1,oU_Q`.
* (xi-f), lines 10895-10898: the inclusion `-|log(q)| in R_{<= -|log(Theta)|}`, hence
  `-|log(q)| <= -|log(Theta)|`, follows formally; this is `C_Theta >= -1`.
* lines 10354-10358: since `|log(q)| > 0`, one may assume `-|log(Theta)| < 0`;
  otherwise `-|log(Theta)| >= 0 > -|log(q)|` is trivial.

SIGN CONVENTION (this is the point of the audit): `-|log(Theta)|` and `-|log(q)|` are
the VALUES of the log-volume itself (log of the measure, with the packet-normalization
above), NOT the negation of a positive magnitude.  Consequences:
* log-volume is **monotone increasing** under inclusion: a larger region has a larger
  (less negative) log-volume (scale by `p^{-1}` adds `+log p`);
* if the q-pilot region is contained in the holomorphic hull `1,oU` (the xi-e
  containment), then `logVolume(qRegion) <= logVolume(hull)`, i.e.
  `-|log(q)| <= -|log(Theta)|` — monotonically, with NO sign flip;
* the content of Cor 3.12 is therefore the **containment xi-e** (the multiradial
  algorithm, (IPL)/(SHE)/(Ind3)), not an arithmetic inequality between positive
  magnitudes.  A model in which the q reading is negative and the Theta reading is a
  POSITIVE average (the hull model's `processionAverage`) has the wrong sign: the
  comparison then becomes vacuous, and a '3.12 reduces to (n+1) <= 24(2n+1)'
  computation is a model error, not a proof.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Prop39SignAuditActual

/-! ## 1. The packet-normalized log-volume of a scaled integral region -/

/-- Log-volume of the region `p^e * O` (the packet normalization of Proposition 3.9, (i):
  `O` has log-volume 0 and multiplication by `p` adds `-log p`). -/
def scalingLogVolume (e : ℤ) (p : ℝ) : ℝ :=
  -(e : ℝ) * Real.log p

/-- Scaling by `p^{-1}` (a larger region) adds `+log p` to the log-volume. -/
theorem scalingLogVolume_inv_smul (e : ℤ) (p : ℝ) :
    scalingLogVolume (e - 1) p = scalingLogVolume e p + Real.log p := by
  unfold scalingLogVolume
  push_cast
  ring

/-- **Monotonicity in the exponent**: if `e' <= e` (i.e. `p^{e'} O` is a LARGER
  region), then the log-volume is at least as large. -/
theorem scalingLogVolume_mono {e e' : ℤ} (hee' : e' ≤ e) {p : ℝ} (hp : 1 ≤ p) :
    scalingLogVolume e p ≤ scalingLogVolume e' p := by
  have hlog : 0 ≤ Real.log p := Real.log_nonneg hp
  unfold scalingLogVolume
  have : (e' : ℝ) ≤ (e : ℝ) := by exact_mod_cast hee'
  nlinarith

/-! ## 2. The abstract monotone direction of the paper inequality -/

/-- **Paper target in log-volume form**: if the q-pilot region is contained in the
  holomorphic hull, then its log-volume is at most the hull's log-volume, i.e.
  `-|log q| <= -|log(Theta)|` (both sides are log-volume VALUES). -/
theorem paper_inequality_of_containment {X : Type*} (logVolume : Set X → ℝ)
    (mono : ∀ {S T : Set X}, S ⊆ T → logVolume S ≤ logVolume T)
    {qRegion hull : Set X} (h : qRegion ⊆ hull) :
    logVolume qRegion ≤ logVolume hull :=
  mono h

/-- The paper inequality written with the two named log-volume values: it is exactly
  `qLog <= thetaLog`, with NO negation of either side. -/
theorem paper_inequality_form (qLog thetaLog : ℝ) (h : qLog ≤ thetaLog) :
    -(-qLog) ≤ -(-thetaLog) := by
  linarith

/-! ## 3. Why a positive-magnitude model makes 3.12 vacuous -/

/-- A positive-magnitude model: if the Theta side is a positive average and the q side
  a negative number, then the comparison holds automatically (no content). -/
theorem positiveMagnitude_comparison_vacuous {qVol thetaVol : ℝ}
    (hq : qVol ≤ 0) (htheta : 0 ≤ thetaVol) : qVol ≤ thetaVol := by
  linarith

/-- Conversely, if the log-volume is increasing under inclusion and the q-region is
  contained in the hull, the paper inequality is the NON-vacuous monotone conclusion
  of Section 2; a model that obtains '3.12 is automatic from `(n+1) <= 24(2n+1)`'
  has reverted the sign convention (positive magnitudes instead of log-volumes). -/
theorem containment_is_the_content {X : Type*} (logVolume : Set X → ℝ)
    (mono : ∀ {S T : Set X}, S ⊆ T → logVolume S ≤ logVolume T)
    {qRegion hull : Set X} (h : qRegion ⊆ hull)
    (hnontriv : logVolume qRegion < logVolume hull → True) :
    logVolume qRegion ≤ logVolume hull :=
  mono h

end

end LeanFormal.IUT.XiFPaper.Mzk1Prop39SignAuditActual