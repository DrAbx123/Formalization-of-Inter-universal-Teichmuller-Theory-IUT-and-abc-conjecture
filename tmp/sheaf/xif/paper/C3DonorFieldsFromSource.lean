import tmp.sheaf.n8.closure.C3Actual
import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.C3Roots
import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput

/-! # C3 donor fields from actual native source data

This file constructs the actual non-tensor part of
SourcePilotRegionDonors:

* the prime p = rational prime of the native selected bad base place;
* the place = that bad base place as a FinitePlaceAtPrime;
* the theta packet (supplied from the actual C3/theater data);
* roots/roots', kummerClass and rootChange (explicit source fields).

The native C3 q is attached to the F-place nativeFPlaceOverBad over the bad
place, while SourcePilotRegionDonors.q must be a FinitePlaceQCandidate at the
base Fmod place.  The frozen tree provides no restriction/descent of that
completion q to the base completion, so q (and therefore roots, rootChange
and Kummer class) remains an exact missing field.  The tensor unit/landing are
taken from the actual NativeTensorLandingDonor field, not from an inequality.

No toy data/True/PUnit/axiom/sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.C3DonorFieldsFromSource

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {V : Type uv}

/-- The rational prime of the native selected bad base place. -/
def nativeC3Prime : Nat :=
  (completionRationalPrime (nativeBadBasePlace X)).val

/-- The actual prime fact for the native selected bad base place. -/
theorem nativeC3Prime_prime : Nat.Prime (nativeC3Prime X) :=
  (completionRationalPrime (nativeBadBasePlace X)).property

/-- Fact instance for the actual native base prime. -/
instance nativeC3PrimeFact : Fact (Nat.Prime (nativeC3Prime X)) :=
  ⟨nativeC3Prime_prime X⟩

/-- The actual base place as a FinitePlaceAtPrime. -/
def nativeC3Place :
    FinitePlaceAtPrime X.S.arithmetic.Fmod (nativeC3Prime X) :=
  ⟨nativeBadBasePlace X, rfl⟩

/-- The actual theta packet supplied by a source theater at (0,0). -/
def nativeC3ThetaPacket (I : OriginalInput l V) :
    FiniteThetaPacket l :=
  (I.theaterAt 0 0).thetaPacket

/-- Non-tensor source fields needed to complete SourcePilotRegionDonors at the
native base place.  q is the missing base-completion q; roots/kummer/rootChange
depend on it and are explicit fields. -/
structure NativeC3NonTensorSourceFields
    (I : OriginalInput l V) where
  q : FinitePlaceQCandidate (nativeC3Place X).val
  roots : NatRootSystem
    (candidateUnits (nativeC3Place X) q)
  roots' : NatRootSystem
    (candidateUnits (nativeC3Place X) q)
  kummerClass : CyclotomicTower
    (CommonPrimeCompletion (nativeC3Place X))
  rootChange : CyclotomicTower
    (CommonPrimeCompletion (nativeC3Place X))
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'
  thetaPacket : FiniteThetaPacket l

/-- The non-tensor donor fields at the actual native base place, with q and its
root/Kummer data supplied as explicit fields. -/
structure NativeC3NonTensorDonors
    (I : OriginalInput l V) where
  p : Nat
  [hp : Fact p.Prime]
  place : FinitePlaceAtPrime X.S.arithmetic.Fmod p
  q : FinitePlaceQCandidate place.val
  thetaPacket : FiniteThetaPacket l
  roots : NatRootSystem
    (candidateUnits place q)
  roots' : NatRootSystem
    (candidateUnits place q)
  kummerClass : CyclotomicTower
    (CommonPrimeCompletion place)
  rootChange : CyclotomicTower
    (CommonPrimeCompletion place)
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'

/-- Construct the non-tensor donor record: p and place are the actual native
bad base place; q/roots/kummer/rootChange are the explicit source fields. -/
def nativeC3NonTensorDonors
    {V : Type uv} {I : OriginalInput l V}
    (S : NativeC3NonTensorSourceFields X I) :
    NativeC3NonTensorDonors X I where
  p := nativeC3Prime X
  hp := ⟨nativeC3Prime_prime X⟩
  place := nativeC3Place X
  q := S.q
  thetaPacket := S.thetaPacket
  roots := S.roots
  roots' := S.roots'
  kummerClass := S.kummerClass
  rootChange := S.rootChange
  rootChange_eq := S.rootChange_eq

/-- The actual p is the rational prime of the native bad base place. -/
theorem nativeC3NonTensorDonors_p
    {V : Type uv} {I : OriginalInput l V}
    (S : NativeC3NonTensorSourceFields X I) :
    (nativeC3NonTensorDonors X S).p = nativeC3Prime X := rfl

/-- The actual place is the native bad base place. -/
theorem nativeC3NonTensorDonors_place
    {V : Type uv} {I : OriginalInput l V}
    (S : NativeC3NonTensorSourceFields X I) :
    (nativeC3NonTensorDonors X S).place = nativeC3Place X := rfl

/-- Actual tensor unit field from the native tensor landing donor. -/
structure NativeC3TensorActual (L : NativeTensorLandingDonor X) where
  tensorUnit : (ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple)ˣ

/-- The actual tensor unit is the donor's tensorUnit. -/
def nativeC3TensorUnitActual (L : NativeTensorLandingDonor X) :
    NativeC3TensorActual X L where
  tensorUnit := L.tensorUnit

/-! ## Exact missing object

1. q : FinitePlaceQCandidate at nativeC3Place.val.
   NativeC3.nativeQActual lives at nativeFPlaceOverBad : FinitePlace F, not at
   the base place nativeBadBasePlace : FinitePlace Fmod; there is no
   restriction/descent map of the q candidate from the F-completion to the
   Fmod-completion in the frozen source.
2. roots and roots' over candidateUnits of that base q.
3. kummerClass and rootChange towers over CommonPrimeCompletion of the base
   place, plus the rootChange = rootSystemDiff roots roots' law.
4. tensorLanding_q for the base q: NativeTensorLandingDonor.tensorLanding_q is
   stated for nativeQ X D at the F-place, not for the base-place q.

No inequality or tensor shortcut substitutes for these fields. -/

end LeanFormal.IUT.XiFPaper.C3DonorFieldsFromSource

end
