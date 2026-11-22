/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.S201RootThetaNormLActual
import Mathlib.Tactic

/-! Reference/object file: laichunwing 07 (theta scaling v(Theta_j) = j^2 v(Theta_1))
and 12 (procession local contributions mu_j = j^2*m/(2l)*log p) realized on the
actual root-theta norm of S201. LANA EtaleTheta/ThetaValues is the semantic
reference; the concrete norms here are the green S201 ones. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LANAThetaScalingReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open scoped BigOperators

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual local q log-volume: log of the q parameter's unit norm.
noncomputable def localQLogVolume : Real :=
  Real.log ‖(sourceRootQUnit T b : rootBase T b)‖

theorem localQLogVolume_constructed :
    localQLogVolume T b = Real.log ‖(sourceRootQUnit T b : rootBase T b)‖ := rfl

/-- The 2l-th root relation at log level: 2l * log(root) = log q. -/
theorem twoL_mul_rootLog_eq_localQLogVolume :
    (2 * (l.value : Real)) * Real.log (rootNormedElementNorm T b) =
      localQLogVolume T b := by
  have h := congrArg Real.log (rootNormedElementNorm_pow_twoL T b)
  rw [Real.log_pow] at h
  simpa [localQLogVolume, rootNormedElementNorm, Nat.cast_mul] using h

/-- 07 theta scaling on the actual root theta values: the log norm of Theta_j is
(j^2/(2l)) times the local q log-volume. -/
theorem localThetaLogVolume_eq_gaussExponent_div_twoL_mul_qLog (j : SignedLabel l.value) :
    Real.log ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖ =
      (gaussExponent j.1 : Real) / (2 * (l.value : Real)) * localQLogVolume T b := by
  rw [rootNormedThetaValueInL_norm, Real.log_zpow]
  have hlog := twoL_mul_rootLog_eq_localQLogVolume T b
  have h2 : (2 * (l.value : Real)) ≠ 0 := by
    have hl : (0 : ℝ) < (l.value : ℝ) := by exact_mod_cast l.prime.pos
    positivity
  have hroot : Real.log (rootNormedElementNorm T b) =
      localQLogVolume T b / (2 * (l.value : Real)) := by
    rw [eq_div_iff h2]
    linarith [hlog]
  rw [hroot]
  field_simp [h2]

/-- 12 local contribution: the level-j contribution is j^2 times the base factor.
theorem localThetaLogVolume_eq_gaussExponent_mul_base (j : SignedLabel l.value) :
    Real.log ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖ =
      (gaussExponent j.1 : Real) *
        (localQLogVolume T b / (2 * (l.value : Real))) := by
  rw [localThetaLogVolume_eq_gaussExponent_div_twoL_mul_qLog]
  ring

end LeanFormal.IUT.XiFPaper.Mzk1LANAThetaScalingReadoutActual