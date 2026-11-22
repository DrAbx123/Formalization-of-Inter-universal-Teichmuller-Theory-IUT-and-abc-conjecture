import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import LeanFormal.IUT.IUTII.Kummer.NatRootSystem
import LeanFormal.IUT.IUTII.Kummer.KummerClass
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import Mathlib

/-!
# C3 stage 3: actual SourcePilotRegionData constructor

This file does not manufacture the missing source data.  It records the exact
donor fields needed by the frozen C3 structure and provides the actual
constructor from those donors.

The unconditional sourcePilotRegion_nonempty is NOT proved here: OriginalInput
does not contain a selected prime/place, a q in the completion, the two root
systems, the Kummer class/root change, or the tensor landing.  The exact no-go
is recorded in C3-STAGE3.md.

If all donors are supplied, the constructor below builds the actual
SourcePilotRegionData with zero sorry.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C3Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Exact donor fields needed to construct SourcePilotRegionData I.

Every field is an actual source datum, not a conclusion.  In particular q is a
FinitePlaceQCandidate in the completion; no Real q is accepted. -/
structure SourcePilotRegionDonors
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  p : Nat
  [hp : Fact p.Prime]
  place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p
  q : FinitePlaceQCandidate place.val
  thetaPacket : FiniteThetaPacket l
  roots : NatRootSystem
    (candidateUnits (K := I.initial.arithmetic.Fmod) place q)
  roots' : NatRootSystem
    (candidateUnits (K := I.initial.arithmetic.Fmod) place q)
  kummerClass : CyclotomicTower
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
  rootChange : CyclotomicTower
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'
  tensorIndex : Type
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex → Type
  tensorPlaces : (i : tensorIndex) → tensorPlaceIndex i →
    FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p
  tensorTuple : (i : tensorIndex) → tensorPlaceIndex i
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ
  tensorLanding : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place →
    ArithmeticTensorTupleBlock tensorPlaces tensorTuple
  tensorLanding_q : tensorLanding
      (q.q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) =
    (tensorUnit : ArithmeticTensorTupleBlock tensorPlaces tensorTuple)

attribute [instance] SourcePilotRegionDonors.hp
attribute [instance] SourcePilotRegionDonors.tensorFintype

/-- Actual constructor: all C3 fields come from the donor record and the
completion q, not from a Real surrogate. -/
noncomputable def sourcePilotRegionDataOfDonors
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    SourcePilotRegionData (l := l) (V := V) I where
  p := D.p
  hp := D.hp
  place := D.place
  q := D.q
  thetaPacket := D.thetaPacket
  qUnit := candidateUnits (K := I.initial.arithmetic.Fmod) D.place D.q
  qUnit_eq := rfl
  roots := D.roots
  roots' := D.roots'
  kummerClass := D.kummerClass
  rootChange := D.rootChange
  rootChange_eq := D.rootChange_eq
  tensorIndex := D.tensorIndex
  tensorFintype := D.tensorFintype
  tensorPlaceIndex := D.tensorPlaceIndex
  tensorPlaces := D.tensorPlaces
  tensorTuple := D.tensorTuple
  tensorUnit := D.tensorUnit
  tensorLanding := D.tensorLanding
  tensorLanding_q := D.tensorLanding_q

/-- Conditional existence, zero sorry: an actual C3 object exists as soon as
the exact source donors exist. -/
theorem sourcePilotRegion_nonempty_of_donors
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    Nonempty (SourcePilotRegionData.{ua, uv, upi, umon, ui, 0, 0}
      (l := l) (V := V) I) :=
  ⟨sourcePilotRegionDataOfDonors (l := l) (V := V) I D⟩

end LeanFormal.IUT.N8Closure.C3Actual
