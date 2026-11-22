/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1ShellArithmeticIdentitiesActual
import Mathlib.Tactic

/-! # A772 hull: scaled (theta-pilot) C3 log-shell tensor region

Diagnosis: `actualC3LogShellTensorRegion` is the UNSCALED tensor of local
log-shells.  lana's theta-pilot uses `scaleEltAt = qroot ^ ((i+1)^2)` on each
tensor factor.  Here we define the genuinely scaled region on the actual C3
block,

  `paperThetaPilotScaledRegion scale = pi_i (scale_i • actualC3LogShell_i)`,

and record the Haar closed form `log μ(scaled) = sum_i (log μ_i(logShell_i) + δ_i)`,
where `δ_i = dim_i * exponent_i * log ||qroot_i||` is the per-factor scaling
shift.  The scaling shift law is an explicit hypothesis (the local scaling law
is not yet imported from lana); the tensor-factorization/arithmetic is proved.
The q side is `-(1/(2l)) log q` from S3137; the shell average identity
`(1/n) sum_j (j²-1) = sFactor(n)-1` is green and recalled. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1ShellArithmeticIdentitiesActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- The genuinely scaled theta-pilot region on the actual C3 block:
`pi_i (scale_i • IEEE_i)`, with `scale_i` the lana `scaleEltAt` value (an actual
element of the local completion). -/
noncomputable def paperThetaPilotScaledRegion
    (scale : (i : C3.tensorIndex) → C3LogShellFiber C3 i) :
    Set (C3LogShellTensorBlock C3) :=
  Set.pi Set.univ (fun i => (scale i) • actualC3LogShell C3 i)

theorem paperThetaPilotScaledRegion_def
    (scale : (i : C3.tensorIndex) → C3LogShellFiber C3 i) :
    paperThetaPilotScaledRegion C3 scale =
      Set.pi Set.univ (fun i => (scale i) • actualC3LogShell C3 i) := rfl

/-- The Haar closed form of the scaled tensor region: a sum of local shell
log-volumes plus the per-factor scaling shifts `delta_i`.  The identity is
proved from the representation `hlog` (tensor factorization + local scaling
law are explicit inputs, not fabricated). -/
theorem scaledRegion_logVolume_eq_sum
    {ι : Type*} [Fintype ι] (shellLog delta : ι → ℝ)
    (logScaled : ℝ)
    (hlog : logScaled = ∑ i : ι, (shellLog i + delta i)) :
    logScaled = (∑ i : ι, shellLog i) + ∑ i : ι, delta i := by
  rw [hlog, Finset.sum_add_distrib]

/-- The paper exponent form of the scaling shift: `delta_i = dim_i * exponent_i *
log ||qroot_i||`.  `dim_i` is the local Q_p-dimension, `exponent_i = (i+1)^2`
in lana notation; the index ordering/exponent is supplied as a function. -/
def thetaScalingDelta
    (dim : C3.tensorIndex → ℝ) (exponent : C3.tensorIndex → ℕ)
    (logqroot : C3.tensorIndex → ℝ) : C3.tensorIndex → ℝ :=
  fun i => dim i * (exponent i : ℝ) * logqroot i

/-- The scaled hull log-volume in the paper exponent form. -/
def paperScaledLogVolume
    (shellLog : C3.tensorIndex → ℝ)
    (dim : C3.tensorIndex → ℝ) (exponent : C3.tensorIndex → ℕ)
    (logqroot : C3.tensorIndex → ℝ) : ℝ :=
  (∑ i : C3.tensorIndex, shellLog i) +
    ∑ i : C3.tensorIndex, thetaScalingDelta dim exponent logqroot i

theorem paperScaledLogVolume_eq_sum
    (shellLog : C3.tensorIndex → ℝ)
    (dim : C3.tensorIndex → ℝ) (exponent : C3.tensorIndex → ℕ)
    (logqroot : C3.tensorIndex → ℝ) :
    paperScaledLogVolume C3 shellLog dim exponent logqroot =
      (∑ i : C3.tensorIndex, shellLog i) +
        ∑ i : C3.tensorIndex, thetaScalingDelta dim exponent logqroot i := rfl

/-- The green p-scaling law of the actual C3 block (`IUT III, Prop 3.9(i)`):
`log μ(p • S) = -dim * log p + log μ(S)`. -/
theorem c3Tensor_logVolume_p_smul
    {S : Set (C3LogShellTensorBlock C3)}
    (hpos : 0 < (actualC3LogShellTensorHaar C3) S)
    (hfin : (actualC3LogShellTensorHaar C3) S < ⊤) :
    Real.log ((actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • S)).toReal =
      -(c3TensorBlockDimension C3 : ℝ) * Real.log (C3.p : ℝ) +
        Real.log ((actualC3LogShellTensorHaar C3) S).toReal :=
  c3Tensor_log_measure_prime_smul (C3 := C3) (actualC3LogShellTensorHaar C3) hpos hfin

/-- Green shell average identity (A766): `(1/n) sum_{j<n} (j²-1) = sFactor(n)-1`. -/
theorem paper_shell_average_identity (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℝ)) *
        (∑ j ∈ Finset.range n, (((j : ℝ) + 1) ^ 2 - 1)) =
      sFactor n - 1 :=
  shell_average_identity n hn

/-- **Comparison reduction**: if the actual theta hull log-volume equals the
scaled closed form and that closed form dominates the q-side reading, then
`qThetaPilotLogVolumeComparison` holds.  The closed form itself is not asserted. -/
theorem qThetaPilotLogVolumeComparison_of_scaledClosedForm
    (scaledLog : ℝ)
    (hθ : thetaPilotHullLogVolumeReal C3 = scaledLog)
    (hcmp : qPilotLogVolumeReading P ≤ scaledLog) :
    qThetaPilotLogVolumeComparison C3 P := by
  unfold qThetaPilotLogVolumeComparison
  rw [hθ]
  exact hcmp

/-- The q-side reading is nonpositive and the scaled closed form is the sum of
local shell logs and positive shifts; if the shell logs are nonnegative (the
`μ(O)=1` normalization), the comparison is automatic. -/
theorem qThetaPilotLogVolumeComparison_of_nonneg_scaledLog
    (scaledLog : ℝ)
    (hθ : thetaPilotHullLogVolumeReal C3 = scaledLog)
    (hNN : 0 ≤ scaledLog) :
    qThetaPilotLogVolumeComparison C3 P :=
  qThetaPilotLogVolumeComparison_of_scaledClosedForm C3 P scaledLog hθ
    (le_trans (qPilotLogVolumeReading_nonpos P) hNN)

def scaledHullRows : List (String × String × String) :=
  [ ("unscaled theta region", "actualC3LogShellTensorRegion = tensorIntegralRegion (actualC3LogShell_i)", "C3LogShellTensorPacketActual"),
    ("lana scaling", "scaleEltAt_i = qroot_i ^ ((i+1)^2) on the i-th tensor factor", "lana Concrete/ThetaRegion.lean:126-132 (READ)"),
    ("scaled region", "pi_i (scale_i • actualC3LogShell_i) on C3LogShellTensorBlock", "DEF (paperThetaPilotScaledRegion)"),
    ("local p-scaling", "log μ(p • S) = -dim*log p + log μ(S)", "GREEN (c3Tensor_log_measure_prime_smul)"),
    ("scaled closed form", "log μ(scaled) = sum_i shellLog_i + sum_i dim_i*exponent_i*log||qroot_i||", "PROVED conditional on tensor factorization/local scaling (scaledRegion_logVolume_eq_sum)"),
    ("shell average", "(1/n) sum_j (j²-1) = sFactor(n)-1", "GREEN (shell_average_identity)"),
    ("q side", "qPilotLogVolumeReading P = -|log q| = -(order * log(residueNormBase))", "GREEN (S3137 + Mzk1QSideExplicitActual)"),
    ("comparison", "qThetaPilotLogVolumeComparison follows if the scaled closed form >= q reading", "PROVED conditional (qThetaPilotLogVolumeComparison_of_scaledClosedForm)"),
    ("remaining", "tensor Haar factorization and local scaling-shift values δ_i (qroot norms); no residue positivity/Szpiro term is asserted", "EXPLICIT PARAMETERS") ]

theorem scaledHullRows_length : scaledHullRows.length = 9 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullActual.scaledRegion_logVolume_eq_sum
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullActual.paper_shell_average_identity
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullActual.qThetaPilotLogVolumeComparison_of_scaledClosedForm

end LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullActual

end