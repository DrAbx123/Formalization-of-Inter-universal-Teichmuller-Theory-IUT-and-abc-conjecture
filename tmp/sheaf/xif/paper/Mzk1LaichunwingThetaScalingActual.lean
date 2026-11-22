/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.O2QrootGlueActual
import tmp.sheaf.xif.paper.ThetaReadoutFromQActual

/-!
# Mzk1LaichunwingThetaScalingActual — O2 theta readout vs laichunwing 07/17 checks

External independent checks (Sage, read-only data from
`tmp/online/laichunwing__IUT-Verification/IUT-Verification-main/`):

* `07_theta_scaling.txt`: at a bad prime, `v(Theta_j) = j^2 * v(Theta_1)`
  for `Theta_j = qroot^{j^2}` (Joshi ATS III Thm 4.2.2.1(4));
* `17_tate_parameter_root.txt`: the 2*ell-th root `qroot` satisfies
  `qroot^(2*ell) = q` with `v(qroot) = v(q)/(2*ell)` (11a1, ell=13).

This file transports these two checked facts onto our actual O2 objects
(`O2QrootGlueActual.qrootElem`, `ThetaReadoutFromQActual.thetaReadoutFromQ`),
using only the already-proved root power and readout formulas.

No new axiom, no comparison, no empty shell. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LaichunwingThetaScalingActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.O2QrootGlueActual
open LeanFormal.IUT.XiFPaper.ThetaReadoutFromQActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open scoped BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- 07: the theta readout at label j is `j^2` times the q log-magnitude
(the valuation scaling `v(Theta_j) = j^2 * v(Theta_1)` in log form). -/
theorem thetaReadout_scaling (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) :
    thetaReadoutFromQ T b j =
      ((IUT.Theta.gaussExp j.1).toNat : Real) * baseQLogMagnitude T b := 
  thetaReadoutFromQ_eq T b j

/-- 17: the root power relation `qroot^(2*ell) = q` in the root extension. -/
theorem qroot_twoL_pow (b : Bad (nativePlaceSelection T)) :
    (qrootElem T b) ^ (2 * l.value) =
      algebraMap (rootBase T b) (rootNormedExtension T b)
        ((qVFamily T b).q : rootBase T b) := 
  qrootElem_pow T b

/-- 17 in logarithmic form: `2*ell * log||qroot|| = log||q||`,
i.e. the root divides the q-log-magnitude by `2*ell`
(the valuation identity `v(qroot) = v(q)/(2*ell)` in norm form). -/
theorem qroot_log_scaling (b : Bad (nativePlaceSelection T))
    (hq : algebraMap (rootBase T b) (rootNormedExtension T b)
      ((qVFamily T b).q : rootBase T b) ≠ 0) :
    (2 * (l.value : Real)) * Real.log ‖qrootElem T b‖ =
      Real.log ‖algebraMap (rootBase T b) (rootNormedExtension T b)
        ((qVFamily T b).q : rootBase T b)‖ := by
  have hqroot : qrootElem T b ≠ 0 := qrootElem_ne_zero T b
  have hnorm : ‖(qrootElem T b) ^ (2 * l.value)‖ =
      ‖algebraMap (rootBase T b) (rootNormedExtension T b)
        ((qVFamily T b).q : rootBase T b)‖ := by
    rw [qrootElem_pow T b]
  calc (2 * (l.value : Real)) * Real.log ‖qrootElem T b‖
      = Real.log (‖qrootElem T b‖ ^ (2 * l.value)) := (Real.log_pow _ _).symm
    _ = Real.log ‖(qrootElem T b) ^ (2 * l.value)‖ := by
        rw [norm_pow]
    _ = Real.log ‖algebraMap (rootBase T b) (rootNormedExtension T b)
        ((qVFamily T b).q : rootBase T b)‖ := hnorm

/-- `_constructed`: both external checks are transported to the actual O2
objects (scaling formula + root-log identity). -/
theorem laichunwing_checks_transported (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) :
    thetaReadoutFromQ T b j =
        ((IUT.Theta.gaussExp j.1).toNat : Real) * baseQLogMagnitude T b ∧
      (qrootElem T b) ^ (2 * l.value) =
        algebraMap (rootBase T b) (rootNormedExtension T b)
          ((qVFamily T b).q : rootBase T b) :=
  ⟨thetaReadout_scaling T b j, qroot_twoL_pow T b⟩

#check thetaReadout_scaling
#check qroot_twoL_pow
#check qroot_log_scaling

end LeanFormal.IUT.XiFPaper.Mzk1LaichunwingThetaScalingActual
end
