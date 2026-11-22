import tmp.sheaf.xif.paper.Mzk1P5ActualPacketTable
import tmp.sheaf.xif.paper.Mzk1P5PacketReadingActual
import tmp.sheaf.xif.paper.Mzk1P5GammaSubsetHullActual
import LeanFormal.IUT.Foundations.LocalFields.ProductIntegerLattice
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellHull
import Mathlib.MeasureTheory.Measure.Haar.Basic
import tmp.sheaf.xif.paper.Mzk1P5BridgeProofActual
import tmp.sheaf.xif.paper.Mzk1Node0609ProductBridgeActual
import tmp.sheaf.xif.paper.Mzk1ProductFiberMultBridgeGapActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P5OTVolumeFinalActual
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
/-- Actual O_t-module normalized log-volume: logarithm of the Haar measure of
the actual O_t-span Γ_t relative to the actual reference lattice C_t. -/
def actualNormalizedLogVolume
    (e : @FinitePadicTensor p hp A ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))
    (μ : Measure ((j : J) → E j)) : Real :=
  Real.log (μ ((gammaP5 hna (finiteSourceImage A e)) : Set ((j : J) → E j))).toReal -
    Real.log (μ ((unitReferenceLattice (E := E) hna) : Set ((j : J) → E j))).toReal
/-- Actual packet reading with the actual O_t-module normalized log-volume. -/
def actualPacketReadingInput
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))
    (μ : Measure ((j : J) → E j)) (qReading : Real) : Prop :=
  PacketReadingInput (actualNormalizedLogVolume A e hna μ) qReading
theorem actualNormalizedLogVolume_eq
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))
    (μ : Measure ((j : J) → E j)) :
    actualNormalizedLogVolume A e hna μ =
      Real.log (μ ((gammaP5 hna (finiteSourceImage A e)) :
          Set ((j : J) → E j))).toReal -
        Real.log (μ ((unitReferenceLattice (E := E) hna) :
          Set ((j : J) → E j))).toReal := rfl
#check actualNormalizedLogVolume
#check actualPacketReadingInput

/-- The actual normalized O_t-module log-volume of Gamma_t equals the q-reading once
the product-Haar bridge and weighted q-sum bridge are supplied. -/
theorem actualNormalizedLogVolume_eq_qReading_of_bridges
    {l : PrimeGeFive} (X : N8NativeInput l)
    {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))
    (μ : Measure ((j : J) → E j))
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l qReading : Real)
    (hPH : ProductHaarToFiberMult X (actualNormalizedLogVolume A e hna μ) b Fdeg l)
    (hW : WeightedQSumBridge (productLocalLogSum X b Fdeg l) qReading) :
    actualNormalizedLogVolume A e hna μ = qReading :=
  hPH.trans hW

#check actualNormalizedLogVolume_eq_qReading_of_bridges
end LeanFormal.IUT.XiFPaper.Mzk1P5OTVolumeFinalActual
end