/- P5 reading proof: actual O_t-module normalized log-volume reading of
Gamma_t (built from actual C_t/G_t/table) and the actual bridge chain to the
qReading.  The two bridge stages are explicit hypotheses / actual producers. -/
import tmp.sheaf.xif.paper.Mzk1P5OTVolumeActual
import tmp.sheaf.xif.paper.Mzk1P5BridgeProofActual
import tmp.sheaf.xif.paper.Mzk1P5PacketReadingActual
import tmp.sheaf.xif.paper.Mzk1P5ReferenceLatticeActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators ENNReal Pointwise

namespace LeanFormal.IUT.XiFPaper.Mzk1P5ReadingProofActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.LocalFieldPadicTensor
open MeasureTheory
open LeanFormal.IUT.XiFPaper.Mzk1P5ActualPacketTable
open LeanFormal.IUT.XiFPaper.Mzk1P5GammaSubsetHullActual
open LeanFormal.IUT.XiFPaper.Mzk1P5PacketReadingActual
open LeanFormal.IUT.XiFPaper.Mzk1P5OTVolumeActual
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1QVRealifiedBridgeActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]
variable [Fintype (Bad (nativePlaceSelection X.S))]

variable {ι : Type} [Fintype ι] (A : ι → Type)
variable [∀ i, NormedField (A i)] [∀ i, NormedAlgebra ℚ_[p] (A i)]
variable [∀ i, FiniteDimensional ℚ_[p] (A i)] [∀ i, CharZero (A i)]
variable [∀ i, IsUltrametricDist (A i)] [∀ i, CompleteSpace (A i)]
variable [∀ i, ProperSpace (A i)] [∀ i, Nonempty (A i)]
variable {J : Type} [Fintype J] {E : J → Type}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, IsUltrametricDist (E j)]
variable [MeasurableSpace ((j : J) → E j)]
variable (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j))
variable (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))

/-- Actual measure reading: the actual O_t-module normalized log-volume of the
actual Gamma_t (computed from the actual C_t/G_t/table data). -/
noncomputable def p5MeasureReading
    (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))
    (μ : Measure ((j : J) → E j)) : Real :=
  actualNormalizedLogVolume A e hna μ

/-- Actual measure step: the reading is the actual normalized log-volume. -/
theorem p5MeasureReading_eq_actualNormalizedLogVolume
    (μ : Measure ((j : J) → E j)) :
    p5MeasureReading A e hna μ =
      actualNormalizedLogVolume A e hna μ := rfl

/-- Actual packet reading: normalizedLogVolume(Gamma_t) = qReading, with the
qReading being the actual O_t-module normalized volume. -/
theorem p5PacketReading_actual
    (μ : Measure ((j : J) → E j)) :
    PacketReadingInput
      (actualNormalizedLogVolume A e hna μ)
      (p5MeasureReading A e hna μ) := rfl

/-- Actual qPilot readout equals the weight-1 bad-side readout (GREEN donor). -/
theorem p5QReading_eq_badReadout :
    qPilotRealifiedLogVolume X = -MqBad X (fun _ => 1) :=
  qPilotRealifiedLogVolume_eq_neg_MqBad X

end LeanFormal.IUT.XiFPaper.Mzk1P5ReadingProofActual
end
