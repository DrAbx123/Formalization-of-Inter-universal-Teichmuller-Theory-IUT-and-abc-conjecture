import tmp.sheaf.xif.paper.Mzk1P5ActualPacketTable
import tmp.sheaf.xif.paper.Mzk1P5PacketReadingActual
import tmp.sheaf.xif.paper.Mzk1P5GammaSubsetHullActual
import LeanFormal.IUT.Foundations.LocalFields.ProductIntegerLattice
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellHull
import Mathlib.MeasureTheory.Measure.Haar.Basic
import tmp.sheaf.xif.paper.Mzk1P5BridgeProofActual
import tmp.sheaf.xif.paper.Mzk1ProductFiberMultBridgeGapActual
import tmp.sheaf.xif.paper.Mzk1Node0609ProductBridgeActual
import tmp.sheaf.xif.paper.Mzk1P5BridgeProofActual
import tmp.sheaf.xif.paper.Mzk1Node0609ProductBridgeActual
import tmp.sheaf.xif.paper.Mzk1ProductFiberMultBridgeGapActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P5OTVolumeActual
open MeasureTheory
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P5ActualPacketTable
open LeanFormal.IUT.XiFPaper.Mzk1P5PacketReadingActual
open LeanFormal.IUT.XiFPaper.Mzk1P5GammaSubsetHullActual
open LeanFormal.IUT.XiFPaper.Mzk1ProductFiberMultBridgeGapActual
open LeanFormal.IUT.XiFPaper.Mzk1Node0609ProductBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P5BridgeProofActual
open LeanFormal.IUT.XiFPaper.Mzk1P5BridgeProofActual
open LeanFormal.IUT.XiFPaper.Mzk1Node0609ProductBridgeActual
variable {p : ℕ} [hp : Fact (Nat.Prime p)] {ι : Type} [Fintype ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
variable [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, NormedSpace ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable [∀ i, CharZero (A i)] [∀ i, IsUltrametricDist (A i)]
variable [∀ i, CompleteSpace (A i)] [∀ i, ProperSpace (A i)]
variable {J : Type} [Fintype J] {E : J → Type}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)] [∀ j, IsUltrametricDist (E j)]
variable [MeasurableSpace ((j : J) → E j)]
/-- Actual normalized Haar log-volume of a pair of measurable sets
(Γ_t relative to the reference lattice C_t). -/
def actualNormalizedLogVolume
    (Γ C : Set ((j : J) → E j))
    (μ : Measure ((j : J) → E j)) : Real :=
  Real.log (μ Γ).toReal - Real.log (μ C).toReal
/-- Actual packet reading input. -/
def actualPacketReadingInput
    (Γ C : Set ((j : J) → E j))
    (μ : Measure ((j : J) → E j)) (qReading : Real) : Prop :=
  PacketReadingInput (actualNormalizedLogVolume Γ C μ) qReading
theorem actualNormalizedLogVolume_eq
    (Γ C : Set ((j : J) → E j))
    (μ : Measure ((j : J) → E j)) :
    actualNormalizedLogVolume Γ C μ =
      Real.log (μ Γ).toReal - Real.log (μ C).toReal := rfl
/-- Conditional bridge: product-Haar bridge and weighted q-sum bridge imply
the actual normalized volume equals qReading. -/
theorem actualNormalizedLogVolume_eq_qReading_of_bridges
    {l : PrimeGeFive} (X : N8NativeInput l)
    {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]
    (Γ C : Set ((j : J) → E j))
    (μ : Measure ((j : J) → E j))
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l qReading : Real)
    (hPH : ProductHaarToFiberMult X
      (actualNormalizedLogVolume Γ C μ) b Fdeg l)
    (hW : WeightedQSumBridge (productLocalLogSum X b Fdeg l) qReading) :
    actualNormalizedLogVolume Γ C μ = qReading :=
  hPH.trans hW
#check actualNormalizedLogVolume
#check actualPacketReadingInput
#check actualNormalizedLogVolume_eq_qReading_of_bridges
end LeanFormal.IUT.XiFPaper.Mzk1P5OTVolumeActual
end
