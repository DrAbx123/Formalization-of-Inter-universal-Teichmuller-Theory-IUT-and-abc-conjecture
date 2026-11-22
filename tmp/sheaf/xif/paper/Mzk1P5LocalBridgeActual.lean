import tmp.sheaf.xif.paper.Mzk1P5OTVolumeActual
import tmp.sheaf.xif.paper.Mzk1QVIndexMapActual
import tmp.sheaf.xif.paper.Mzk1Node0609ProductBridgeActual
import tmp.sheaf.xif.paper.Mzk1QVRealifiedBridgeActual
import tmp.sheaf.xif.paper.S3133RealifiedQPilotLogVolumeActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P5LocalBridgeActual
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.LocalFieldPadicTensor
open MeasureTheory
open LeanFormal.IUT.XiFPaper.Mzk1QVIndexMapActual
open LeanFormal.IUT.XiFPaper.Mzk1P5OTVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1Node0609ProductBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1QVRealifiedBridgeActual
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {p : Nat} [Fact p.Prime]
variable [Fintype (Bad (nativePlaceSelection X.S))]
variable [DecidableEq (Bad (nativePlaceSelection X.S))]
variable [DecidableEq (FinitePlaceAtPrime X.S.arithmetic.F p)]
variable (L : NativeBadLift X.S.arithmetic (nativePlaceSelection X.S))
variable (hp : ∀ b : Bad (nativePlaceSelection X.S),
  (completionRationalPrime (L.lift b)).val = p)
variable (b : FinitePlaceAtPrime X.S.arithmetic.F p →
  Bad (nativePlaceSelection X.S))
/-- Local product-Haar/fiber-mult bridge with explicit `L`, `p`, `hp` and
decidable-equality instances; no inhabitant is asserted. -/
def LocalProductHaarToFiberMult
    (X : N8NativeInput l)
    (L : NativeBadLift X.S.arithmetic (nativePlaceSelection X.S))
    (p : Nat) [Fact p.Prime]
    [Fintype (Bad (nativePlaceSelection X.S))]
    [DecidableEq (Bad (nativePlaceSelection X.S))]
    [DecidableEq (FinitePlaceAtPrime X.S.arithmetic.F p)]
    (hp : ∀ b : Bad (nativePlaceSelection X.S),
      (completionRationalPrime (L.lift b)).val = p)
    (b : FinitePlaceAtPrime X.S.arithmetic.F p →
      Bad (nativePlaceSelection X.S))
    (localLogSum : Real) (Fdeg l : Real) : Prop :=
  localLogSum = (1 / (2 * l)) *
    (∑ i : FinitePlaceAtPrime X.S.arithmetic.F p,
      fiberMult X L p hp i / Fdeg *
        Real.log (residueNormBase (b i).1))
/-- Actual bridge theorem with both bridges as explicit hypotheses. -/
theorem actualNormalizedLogVolume_eq_qPilot_of_localBridges
    {ι : Type} [Fintype ι] (A : ι → Type)
    [∀ i, NormedField (A i)] [∀ i, NormedAlgebra ℚ_[p] (A i)]
    [∀ i, FiniteDimensional ℚ_[p] (A i)] [∀ i, CharZero (A i)]
    [∀ i, IsUltrametricDist (A i)] [∀ i, CompleteSpace (A i)]
    [∀ i, ProperSpace (A i)]
    {J : Type} [Fintype J] {E : J → Type}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, IsUltrametricDist (E j)]
    [MeasurableSpace ((j : J) → E j)]
    (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))
    (μ : Measure ((j : J) → E j))
    (Fdeg l : Real)
    (hPH : LocalProductHaarToFiberMult X L p hp b
      (- actualNormalizedLogVolume A e hna μ) Fdeg l)
    (hW : WeightedQSumBridge
      ((1 / (2 * l)) *
        (∑ i : FinitePlaceAtPrime X.S.arithmetic.F p,
          fiberMult X L p hp i / Fdeg *
            Real.log (residueNormBase (b i).1)))
      (MqBad X (fun _ => 1))) :
    actualNormalizedLogVolume A e hna μ = qPilotRealifiedLogVolume X := by
  have hS : -actualNormalizedLogVolume A e hna μ =
      (1 / (2 * l)) *
        (∑ i : FinitePlaceAtPrime X.S.arithmetic.F p,
          fiberMult X L p hp i / Fdeg *
            Real.log (residueNormBase (b i).1)) := hPH
  have hS' : actualNormalizedLogVolume A e hna μ =
      -((1 / (2 * l)) *
        (∑ i : FinitePlaceAtPrime X.S.arithmetic.F p,
          fiberMult X L p hp i / Fdeg *
            Real.log (residueNormBase (b i).1))) := by linarith
  have hW' : ((1 / (2 * l)) *
        (∑ i : FinitePlaceAtPrime X.S.arithmetic.F p,
          fiberMult X L p hp i / Fdeg *
            Real.log (residueNormBase (b i).1))) =
      MqBad X (fun _ => 1) := hW
  rw [qPilotRealifiedLogVolume_eq_neg_MqBad X]
  rw [hS', hW']
#check LocalProductHaarToFiberMult
#check actualNormalizedLogVolume_eq_qPilot_of_localBridges
end LeanFormal.IUT.XiFPaper.Mzk1P5LocalBridgeActual
end