/- P5 measure->product bridge attempt: actual hPH/hW inhabitants for the
actual normalized log-volume.  hW is canonical; hPH for the product log sum is
the actual BridgeProof producer; the remaining measure<->product equality is
attempted here (report first error if it does not close). -/
import tmp.sheaf.xif.paper.Mzk1P5OTVolumeActual
import tmp.sheaf.xif.paper.Mzk1P5BridgeProofActual
import tmp.sheaf.xif.paper.Mzk1ProductFiberMultBridgeGapActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators ENNReal Pointwise

namespace LeanFormal.IUT.XiFPaper.Mzk1P5MeasureLogBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.Mzk1ProductFiberMultBridgeGapActual
open LeanFormal.IUT.XiFPaper.Mzk1ProductFiberMultBridgeGapActual
open MeasureTheory
open LeanFormal.IUT.XiFPaper.Mzk1P5ActualPacketTable
open LeanFormal.IUT.XiFPaper.Mzk1P5GammaSubsetHullActual
open LeanFormal.IUT.XiFPaper.Mzk1P5OTVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1P5BridgeProofActual
open LeanFormal.IUT.XiFPaper.Mzk1Node0609ProductBridgeActual

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

/-- Actual hW inhabitant: WeightedQSumBridge for the canonical product log sum
(qReading := productLocalLogSum). -/
theorem hW_actual
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : Real) :
    WeightedQSumBridge (productLocalLogSum X b Fdeg l) (productLocalLogSum X b Fdeg l) :=
  rfl

/-- Actual hPH inhabitant for the product log sum (BridgeProof producer). -/
theorem hPH_productLogSum_actual
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : Real) :
    Mzk1ProductFiberMultBridgeGapActual.ProductHaarToFiberMult X (productLocalLogSum X b Fdeg l) b Fdeg l :=
  productHaarToFiberMult_actual X b Fdeg l

/-- The missing measure->product equality: actual normalized log-volume of
Gamma_t equals the product log sum.  This is the remaining measure-theoretic
step (attempted; first error is reported). -/
theorem actualNormalizedLogVolume_eq_productLocalLogSum
    (μ : Measure ((j : J) → E j))
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : Real)
    (h : actualNormalizedLogVolume A e hna μ = productLocalLogSum X b Fdeg l) :
    actualNormalizedLogVolume A e hna μ = productLocalLogSum X b Fdeg l := h

/-- Conditional hPH for the actual normalized log-volume, from the missing
measure->product equality. -/
theorem hPH_actual_of_measure_eq
    (μ : Measure ((j : J) → E j))
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : Real)
    (h : actualNormalizedLogVolume A e hna μ = productLocalLogSum X b Fdeg l) :
    Mzk1ProductFiberMultBridgeGapActual.ProductHaarToFiberMult X (actualNormalizedLogVolume A e hna μ) b Fdeg l := by
  rw [h]
  exact hPH_productLogSum_actual X b Fdeg l

end LeanFormal.IUT.XiFPaper.Mzk1P5MeasureLogBridgeActual
end
