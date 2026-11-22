import tmp.sheaf.xif.paper.Mzk1QVMultiplicityBridgeActual
import tmp.sheaf.n8.closure.NativeSourceReductionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1QVIndexMapActual
open LeanFormal.IUT.XiFPaper.Mzk1QVMultiplicityBridgeActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
variable {l : PrimeGeFive} (X : N8NativeInput l)
variable (L : NativeBadLift X.S.arithmetic (nativePlaceSelection X.S))
/-- Index map from bad native places to the finite-place subtype over F, given
the prime identity for the lying-over lifts. -/
def badPlaceIndex (p : Nat)
    (hp : ∀ b : Bad (nativePlaceSelection X.S),
      (completionRationalPrime (L.lift b)).val = p) :
    Bad (nativePlaceSelection X.S) → FinitePlaceAtPrime X.S.arithmetic.F p :=
  fun b => ⟨L.lift b, hp b⟩
/-- The q_v multiplicity transported to the lifted F-place. -/
def qVMultAt (b : Bad (nativePlaceSelection X.S)) : ℝ :=
  (qVEffectiveMultiplicity X b : ℝ)
variable [Fintype (Bad (nativePlaceSelection X.S))]
variable [DecidableEq (Bad (nativePlaceSelection X.S))]
/-- Fiber-sum multiplicity over all finite places at `p`: a bad place contributes
its q_v multiplicity to its lifted F-place, and all other places contribute zero. -/
noncomputable def fiberMult (p : Nat)
    [Fintype (Bad (nativePlaceSelection X.S))]
    [DecidableEq (Bad (nativePlaceSelection X.S))]
    [DecidableEq (FinitePlaceAtPrime X.S.arithmetic.F p)]
    (hp : ∀ b : Bad (nativePlaceSelection X.S),
      (completionRationalPrime (L.lift b)).val = p)
    (i : FinitePlaceAtPrime X.S.arithmetic.F p) : Real :=
  ∑ b in (Finset.univ.filter (fun b : Bad (nativePlaceSelection X.S) =>
      badPlaceIndex X L p hp b = i)),
    (qVEffectiveMultiplicity X b : Real)
/-- A finite place outside the bad image has zero fiber multiplicity. -/
theorem fiberMult_eq_zero_of_not_mem (p : Nat)
    [DecidableEq (FinitePlaceAtPrime X.S.arithmetic.F p)]
    (hp : ∀ b : Bad (nativePlaceSelection X.S),
      (completionRationalPrime (L.lift b)).val = p)
    (i : FinitePlaceAtPrime X.S.arithmetic.F p)
    (h : ∀ b : Bad (nativePlaceSelection X.S), badPlaceIndex X L p hp b ≠ i) :
    fiberMult X L p hp i = 0 := by
  unfold fiberMult
  rw [Finset.sum_filter]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : badPlaceIndex X L p hp b = i
  · exact (h b hb).elim
  · simp [hb]
#check fiberMult
#check fiberMult_eq_zero_of_not_mem
#check badPlaceIndex
#check qVMultAt
end LeanFormal.IUT.XiFPaper.Mzk1QVIndexMapActual
end