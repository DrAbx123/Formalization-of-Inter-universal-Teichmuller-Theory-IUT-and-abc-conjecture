/- H1a minimum-valuation support and P5 actual-inequality support.
The H1a min rP5 is the coordinatewise inf over all actual source vectors;
every source valuation is bounded below by it.  The P5 side packages the
actual signed inequality together with the carrier glue. -/
import tmp.sheaf.xif.paper.Node09H1bVolumeActual
import tmp.sheaf.xif.paper.Node09H1bVolumeInequalityActual
import tmp.sheaf.xif.paper.Mzk1P5InequalityCarrierGlueActual
import tmp.sheaf.xif.paper.Mzk1KummerRealizationActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1aMinP5InequalitySupportActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Node09H1aSourceVectorsActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1P4WeightedReadoutProofActual
open LeanFormal.IUT.XiFPaper.Mzk1P5PacketReadingActual
open LeanFormal.IUT.XiFPaper.Mzk1P4JqLatticeActual
open LeanFormal.IUT.XiFPaper.Node09H1bVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1P5InequalityCarrierGlueActual

variable {p : Nat} [Fact p.Prime] {ι : Type} [Fintype ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
variable [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable [∀ i, CharZero (A i)] [∀ i, IsUltrametricDist (A i)]
variable [∀ i, CompleteSpace (A i)] [∀ i, ProperSpace (A i)]
variable {J : Type} [Fintype J] {E : J → Type}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)] [∀ j, IsUltrametricDist (E j)]
variable [∀ j, CharZero (E j)] [∀ j, CompleteSpace (E j)] [∀ j, ProperSpace (E j)]

/-- H1a minimum valuation is a lower bound for every actual source-vector
valuation at each tensor coordinate. -/
theorem rP5_le_sourceFactorValuation
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (basis : Module.Basis (FinitePadicTensorIndex (p := p) A) ℚ_[p]
      (FinitePadicTensor (p := p) A))
    (hne : (Finset.univ : Finset (FinitePadicTensorIndex (p := p) A)).Nonempty)
    (j : J) (k : FinitePadicTensorIndex (p := p) A) :
    rP5 A e basis hne j ≤ sourceFactorValuation A e basis k j :=
  Finset.inf'_le (fun k => sourceFactorValuation A e basis k j) (Finset.mem_univ k)

/-- H1a minimum-valuation budget is finite and attained by an actual source
column. -/
theorem rP5_attained
    (e : FinitePadicTensor (p := p) (M := A) ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (basis : Module.Basis (FinitePadicTensorIndex (p := p) A) ℚ_[p]
      (FinitePadicTensor (p := p) A))
    (hne : (Finset.univ : Finset (FinitePadicTensorIndex (p := p) A)).Nonempty)
    (j : J) :
    ∃ k, rP5 A e basis hne j = sourceFactorValuation A e basis k j :=
  rP5_eq_sourceFactorValuation A e basis hne j

/-- P5 actual signed inequality, packaged with carrier glue. -/
theorem p5_actual_inequality_support
    {l : PrimeGeFive} (X : N8NativeInput l)
    [Fintype (Bad (nativePlaceSelection X.S))]
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] (R : PaperKummerReading T) :
    R.qReading ≤ R.thetaReading ∧
      PacketReadingInput (qPilotRealifiedLogVolume X)
        (weightedReadout X (fun _ => 1)) ∧
      Real.log (jqIndex (X := X) : Real) =
        -qPilotRealifiedLogVolume X :=
  ⟨p5_signed_inequality T R,
    p5_carrier_qReading_glue X,
    p5_carrier_jqLog_glue X⟩

#print axioms rP5_le_sourceFactorValuation
#print axioms rP5_attained
#print axioms p5_actual_inequality_support

end LeanFormal.IUT.XiFPaper.Node09H1aMinP5InequalitySupportActual
end
