import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# xi-f formal step and the C_Theta >= -1 conclusion (abstract real form)

This is the formal (order-theoretic) content of IUT III, Corollary 3.12,
Step (xi-d)-(xi-f): the q-pilot log-volume is an element of the set
`R_{<= -|log Theta|}` of possible Theta-pilot log-volumes, hence
`-|log q| <= -|log Theta|`; with the calibration
`C_Theta * |log q| = -|log Theta|` and `|log q| > 0`, this gives
`-1 <= C_Theta`.

No paper-specific containment/hull construction is asserted here; the xi-e
inclusion is an explicit hypothesis (the input of the xi-f formal step).
No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1XiFFormalStepActual

noncomputable section

/-- `R_{<= lambda}`: the paper's set `{lambda' | lambda' <= lambda}` of
possible pilot log-volumes below `lambda`. -/
def regionLe (thetaLog : Real) : Set Real := Set.Iic thetaLog

@[simp] theorem mem_regionLe {thetaLog lambda : Real} :
    lambda ∈ regionLe thetaLog ↔ lambda ≤ thetaLog := Iff.rfl

theorem regionLe_mono {thetaLog thetaLog' : Real} (h : thetaLog ≤ thetaLog') :
    regionLe thetaLog ⊆ regionLe thetaLog' :=
  fun _ hx => le_trans hx h

/-- **xi-f formal step**: membership of the q-pilot log-volume in the set of
possible Theta-pilot log-volumes gives the inequality. -/
theorem xi_f_formal_step {thetaLog qLog : Real}
    (h : qLog ∈ regionLe thetaLog) : qLog ≤ thetaLog := h

/-- Calibrated pilot data: `logTheta = -|log Theta|`, `logq = -|log q|`,
`absLogq = |log q| = log q / (2l)`, and `C * |log q| = -|log Theta|`. -/
structure CalibratedPilots where
  logTheta : Real
  logq : Real
  absLogq : Real
  C : Real
  hAbsPos : 0 < absLogq
  hq : logq = -absLogq
  hC : C * absLogq = logTheta

/-- Possible log-volumes of a calibrated Theta-pilot. -/
def possibleLogVolumes (D : CalibratedPilots) : Set Real :=
  regionLe D.logTheta

/-- xi-e inclusion specialized to the calibrated data. -/
theorem xi_f_mem_implies_le (D : CalibratedPilots)
    (h : D.logq ∈ regionLe D.logTheta) : D.logq ≤ D.logTheta :=
  xi_f_formal_step h

/-- **Cor 3.12 constant conclusion from the xi-f inclusion**: if the q-pilot
log-volume lies in the Theta-pilot possible set (with `logq = -|log q|`),
then `C >= -1`. -/
theorem xi_f_C_ge_neg_one (D : CalibratedPilots)
    (h : D.logq ∈ regionLe D.logTheta) : -1 ≤ D.C := by
  have hqle : D.logq ≤ D.logTheta := xi_f_formal_step h
  have hqle' : -D.absLogq ≤ D.logTheta := by
    simpa [D.hq] using hqle
  have hmul : (-1 : Real) * D.absLogq ≤ D.C * D.absLogq := by
    calc (-1 : Real) * D.absLogq = -D.absLogq := by ring
      _ ≤ D.logTheta := hqle'
      _ = D.C * D.absLogq := by rw [D.hC]
  exact le_of_mul_le_mul_right hmul D.hAbsPos

end

end LeanFormal.IUT.XiFPaper.Mzk1XiFFormalStepActual
