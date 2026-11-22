/- U-R C1 feed (small): the actual packet hull satisfies the Step-V paper bound. -/
import tmp.sheaf.xif.paper.URPacketDefs
import tmp.sheaf.xif.paper.URPhiAction
import tmp.sheaf.xif.paper.Mzk1P6StepVBoundConsumerActual
import tmp.sheaf.n8.closure.NativeInput
import Mathlib.Tactic

set_option maxHeartbeats 2000000
noncomputable section
namespace LeanFormal.IUT.XiFPaper.URC1Feed
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1P6StepVBoundConsumerActual
open LeanFormal.IUT.XiFPaper.URPacketDefs
open LeanFormal.IUT.XiFPaper.URPhiAction

universe u v w
variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [MeasurableSpace (urBlock X)] [BorelSpace (urBlock X)]

theorem ur_c1_feed
    {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[urP X] (E j)]
    [∀ j, FiniteDimensional ℚ_[urP X] (E j)] [∀ j, ProperSpace (E j)]
    (e : urBlock X ≃ₐ[ℚ_[urP X]] ((j : J) → E j)) :
    arithmeticTupleNormalizedLogVolume (urPlaces X) (urTuple X)
        MeasureTheory.Measure.addHaar
        (arithmeticTupleHolomorphicHull (urPlaces X) (urTuple X) e
          (arithmeticTupleStepVPossibleImages (urPlaces X) (urTuple X)
            urIst (urVarpi X) (urPhi X))) ≤
      (-localNormOrder (urP X) (urVarpi X) +
          ∑ i, localNormOrder (urP X)
            (arithmeticTupleLocalDifferent (urPlaces X) (urTuple X) i) + 1) *
        Real.log (urP X : Real) +
        ∑ i ∈ (Finset.univ : Finset Unit),
          (3 + Real.log (logShellRamificationExponent
            (K := CommonPrimeCompletion ((urPlaces X) i ((urTuple X) i)))
            (p := urP X) : Real)) :=
  p6_stepV_bound_consumer (urPlaces X) (urTuple X) e urIst (urVarpi X)
    (urHvarpi X) (urPhi X) (urPhi_nonempty X) (urPhi_preserves X) Finset.univ
    (fun i hi => absurd (Finset.mem_univ i) hi)

#print axioms ur_c1_feed
end LeanFormal.IUT.XiFPaper.URC1Feed
end
