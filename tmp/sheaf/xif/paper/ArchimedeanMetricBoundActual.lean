/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! 06_archimedean_metric (laichunwing IUT-Verification) as Lean numerics:
IUT IV Prop 1.5(iii): the direct-sum metric is bounded by 2^(|I|-1) times the
tensor metric (equality for pure tensors). We formalize the numeric bound for
the pure-tensor case and its log form, and tie the archimedean real dimension
2*dim to the C3 packet dimension used by the O6 hull-radius normalization. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.ArchimedeanMetricBoundActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open MeasureTheory

/-! ## 1. The archimedean direct-sum/tensor metric bound -/

/-- Archimedean metric bound factor 2^(|I|-1) times the tensor squared norm. -/
def archimedeanMetricBound (n : Nat) (tensorSq : Real) : Real :=
  (2 : Real) ^ (n - 1) * tensorSq

theorem one_le_two_pow_pred (n : Nat) (hn : 1 <= n) :
    (1 : Real) <= (2 : Real) ^ (n - 1) :=
  one_le_pow_of_one_le (by norm_num : (1 : Real) <= 2) (n - 1)

/-- Pure tensors: tensor metric <= 2^(|I|-1) * tensor metric (equality plus
the nonnegative factor). -/
theorem pureTensor_le_archimedeanMetricBound (n : Nat) (hn : 1 <= n)
    (tensorSq : Real) (h : 0 <= tensorSq) :
    tensorSq <= archimedeanMetricBound n tensorSq := by
  unfold archimedeanMetricBound
  calc tensorSq = 1 * tensorSq := (one_mul _).symm
    _ <= (2 : Real) ^ (n - 1) * tensorSq :=
      mul_le_mul_of_nonneg_right (one_le_two_pow_pred n hn) h

/-- Log form of the archimedean bound: the factor contributes (n-1)*log 2. -/
theorem archimedeanMetricBound_log (n : Nat) (x : Real) (hx : 0 < x) :
    Real.log (archimedeanMetricBound n x) =
      ((n - 1 : Nat) : Real) * Real.log 2 + Real.log x := by
  unfold archimedeanMetricBound
  rw [Real.log_mul (by positivity) hx.ne', Real.log_pow]
  ring

/-! ## 2. Archimedean real dimension vs C3 packet dimension -/

/-- The real (archimedean) dimension of a complex tensor of dimension d. -/
def archimedeanRealDimension (d : Nat) : Nat := 2 * d

theorem archimedeanRealDimension_eq (d : Nat) :
    archimedeanRealDimension d = 2 * d := rfl

theorem archimedeanRealDimension_pos (d : Nat) (hd : 0 < d) :
    0 < archimedeanRealDimension d := by
  unfold archimedeanRealDimension
  omega

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance archMetricMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance archMetricBorelSpace : BorelSpace (C3LogShellTensorBlock C3) :=
  ⟨rfl⟩

/-- The C3 block's real dimension is twice the Q_p-dimension (archimedean
analogue of the metric comparison). -/
theorem c3TensorBlock_realDimension_eq (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    archimedeanRealDimension (c3TensorBlockDimension C3) =
      2 * c3TensorBlockDimension C3 := rfl

/-- The p-adic log-volume normalization constant is the Q_p-dimension times
log p; the exponent of p-scaling matches the packet normalization. -/
theorem c3PacketDimension_log_p (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    Real.log ((C3.p : Real) ^ (c3TensorBlockDimension C3 : Nat)) =
      (c3TensorBlockDimension C3 : Real) * Real.log (C3.p : Real) := by
  rw [Real.log_pow]

end LeanFormal.IUT.XiFPaper.ArchimedeanMetricBoundActual