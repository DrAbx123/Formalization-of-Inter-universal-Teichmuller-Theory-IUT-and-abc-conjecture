import tmp.sheaf.n8.closure.EtaTensorNormActual
import tmp.sheaf.n8.closure.EtaGaussianSpecialValueVolume
import Mathlib

/-!
# Conditional Gaussian tensor-volume formula

Uses the actual tensor block/determinant interface from EtaTensorNormActual and
the actual a^(j^2) Gaussian completion power from EtaGaussianSpecialValueVolume.
The only remaining inputs are:

1. the tensor-block normalized volume formula (primespine tensor-norm interface);
2. ThetaPacketIdentification (source real theta scale = finite theta packet).

No arbitrary g or volume is introduced.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.EtaTensorBlockDetActual
open LeanFormal.IUT.N8Closure.EtaTensorNormActual
open LeanFormal.IUT.N8Closure.EtaGaussianSpecialValueVolume
open LeanFormal.IUT.N8Closure.SourcePilotRegion

namespace LeanFormal.IUT.N8Closure.EtaGaussianVolumeConditional

universe u ua uv upi umon ui

variable {p : Nat} [Fact p.Prime]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
  [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]

/-- The actual Gaussian exponent of a signed label. -/
def gaussianExponent {l : PrimeGeFive} (j : SignedLabel l.value) : Nat :=
  (gaussExponent j.1).toNat

/-- Actual a^(j^2) in the tensor factor. -/
def gaussianTensorValue {l : PrimeGeFive} (j : ι) (a : A j)
    (jL : SignedLabel l.value) : A j :=
  a ^ gaussianExponent jL

/-- Conditional tensor-block normalized volume formula: the normalized log of
the actual tensor determinant equals log factor norm divided by d_j.  This is
the exact primespine tensor-norm interface, not assumed globally. -/
def TensorBlockVolumeFormula (j : ι) (g : A j) : Prop :=
  Real.log ‖tensorDet (p := p) A j g‖ / (totalDim (p := p) A : ℝ) =
    Real.log ‖g‖ / (factorDim (p := p) A j : ℝ)

/-- Conditional BPS volume formula for the actual a^(j^2) Gaussian value. -/
theorem gaussianVolumeDiff_conditional {l : PrimeGeFive}
    (j : ι) (jL : SignedLabel l.value) (a : A j)
    (hvolume : TensorBlockVolumeFormula (p := p) A j
      (gaussianTensorValue (A := A) j a jL)) :
    Real.log ‖tensorDet (p := p) A j (gaussianTensorValue (A := A) j a jL)‖ /
        (totalDim (p := p) A : ℝ) =
      (gaussianExponent jL : ℝ) * Real.log ‖a‖ /
        (factorDim (p := p) A j : ℝ) := by
  rw [hvolume, gaussianTensorValue, norm_pow, Real.log_pow]

/-- Exact remaining tensor-norm gap: a point where the conditional volume
formula is not supplied. -/
def TensorBlockVolumeFormulaGap : Prop :=
  ∃ (j : ι) (g : A j), ¬ TensorBlockVolumeFormula (p := p) A j g

section ThetaGap

variable {l : PrimeGeFive} {V : Type uv}
variable {I : LeanFormal.IUT.Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Exact remaining source theta gap: ThetaPacketIdentification. -/
def ThetaPacketIdentificationGap : Prop :=
  missingActualThetaValue (I := I) C3

theorem ThetaPacketIdentificationGap_obligation :
    ThetaPacketIdentificationGap C3 :=
  missingActualThetaValue_obligation (I := I) C3

end ThetaGap

end LeanFormal.IUT.N8Closure.EtaGaussianVolumeConditional
