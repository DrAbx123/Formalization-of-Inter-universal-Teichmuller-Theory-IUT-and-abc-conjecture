/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.Mzk1GapDirectComputationActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellHaarIndex
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexArithmetic
import Mathlib.Tactic

/-! # A770 hull: Haar normalization and the gap comparison

Green local facts:
* `measure_integralLogShell_eq_index_mul`: any additive Haar `mu` satisfies
  `mu(integralLogShell) = logShellIntegerIndex * mu(O)`;
* `logShellIntegerIndex_pos`: the index is a positive natural.

Consequently, in the normalization `mu(O) = 1` every factor log-shell has
nonnegative log-measure, so the Theta-side hull log-volume is `>= 0`; the q side
is `<= 0` (green S3137).  Hence the paper comparison holds *trivially* in this
normalization.  The paper normalization is different (it contains the different/
unit terms and is not `mu(O)=1` at all tensor factors); this file records the
trivial-normalization theorem and the normalization comparison table. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GapNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open scoped ENNReal BigOperators

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- **Theta side is `>= 0` in the `mu(O)=1` normalization.**  If the Theta hull
log-volume is a sum of logs of positive integral indices (the tensor-product
formula of the local `measure_integralLogShell_eq_index_mul`), then it is
nonnegative because each `logShellIntegerIndex >= 1`. -/
theorem thetaHullLogVolume_nonneg_of_sum_log_index
    {ι : Type*} [Fintype ι] (idx : ι → Nat)
    (hrep : thetaPilotHullLogVolumeReal C3 =
      ∑ i : ι, Real.log (idx i : Real))
    (hpos : ∀ i : ι, 1 <= idx i) :
    0 <= thetaPilotHullLogVolumeReal C3 := by
  rw [hrep]
  exact Finset.sum_nonneg fun i _ => Real.log_nonneg (by exact_mod_cast hpos i)

/-- **The paper comparison follows from a nonnegative Theta side** (q side is
nonpositive by S3137). -/
theorem qThetaPilotLogVolumeComparison_of_theta_nonneg
    (hθ : 0 <= thetaPilotHullLogVolumeReal C3) :
    qThetaPilotLogVolumeComparison C3 P := by
  unfold qThetaPilotLogVolumeComparison
  exact le_trans (qPilotLogVolumeReading_nonpos P) hθ

/-- **A770(a): the comparison holds in the `mu(O)=1` normalization**, from the
local index representation with all indices at least one.  The representation
is an explicit hypothesis (the tensor-product factorization is the missing
measure-theoretic input); no comparison proof is fabricated without it. -/
theorem qThetaPilotLogVolumeComparison_of_muO_one
    {ι : Type*} [Fintype ι] (idx : ι → Nat)
    (hrep : thetaPilotHullLogVolumeReal C3 =
      ∑ i : ι, Real.log (idx i : Real))
    (hpos : ∀ i : ι, 1 <= idx i) :
    qThetaPilotLogVolumeComparison C3 P :=
  qThetaPilotLogVolumeComparison_of_theta_nonneg C3 P
    (thetaHullLogVolume_nonneg_of_sum_log_index C3 idx hrep hpos)

/-- Specialization to a single positive index: `theta = log(mu(logShell)) >= 0`. -/
theorem qThetaPilotLogVolumeComparison_of_single_index
    (idx : Nat) (hidx : 1 <= idx)
    (hrep : thetaPilotHullLogVolumeReal C3 = Real.log (idx : Real)) :
    qThetaPilotLogVolumeComparison C3 P := by
  refine qThetaPilotLogVolumeComparison_of_theta_nonneg C3 P ?_
  rw [hrep]
  exact Real.log_nonneg (by exact_mod_cast hidx)

def normalizationRows : List (String × String × String) :=
  [ ("local Haar formula", "mu(integralLogShell) = logShellIntegerIndex * mu(O) (any additive Haar)", "GREEN (measure_integralLogShell_eq_index_mul)"),
    ("index positivity", "logShellIntegerIndex >= 1", "GREEN (logShellIntegerIndex_pos)"),
    ("mu(O)=1 normalization", "every local logShell log-measure >= 0; theta hull log-volume >= 0", "PROVED (thetaHullLogVolume_nonneg_of_sum_log_index)"),
    ("q side", "qPilotLogVolumeReading P <= 0 (strictly < 0 for the actual q)", "GREEN (S3137)"),
    ("comparison in mu(O)=1", "qThetaPilotLogVolumeComparison holds trivially: 0 >= negative", "PROVED conditional on tensor index representation"),
    ("paper normalization", "uses different/unit terms and local normalizations, NOT mu(O)=1 at all factors; theta side can be negative", "NOT COVERED / definitional gap"),
    ("required paper data", "local O-measures mu_i(O_i), different exponent d_I, archimedean log(sqrt 2*pi), 1/nC procession weights", "PAPER NORMALIZATION REQUIREMENTS"),
    ("meaning", "mu(O)=1 makes the comparison weak/trivial and is not the paper normalization", "STRUCTURAL") ]

theorem normalizationRows_length : normalizationRows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapNormalizationActual.thetaHullLogVolume_nonneg_of_sum_log_index
#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapNormalizationActual.qThetaPilotLogVolumeComparison_of_theta_nonneg
#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapNormalizationActual.qThetaPilotLogVolumeComparison_of_muO_one

end LeanFormal.IUT.XiFPaper.Mzk1GapNormalizationActual

end