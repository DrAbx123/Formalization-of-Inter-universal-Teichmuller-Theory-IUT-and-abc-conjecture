import tmp.sheaf.n8.closure.N8NativeClosure
import tmp.sheaf.n8.closure.NativeC1
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction

/-!
# C10 native bridge proof / exact no-go

Goal: construct NativeOldC1Bridge X from the native root X.

What is actually constructible:
- OriginalInput from explicit donors NativeOriginalInputDonors: a
  SourceDefinition31Data initial, its arithmetic equality, and an index
  equivalence X.family.index ≃ Int × Int.
- SourceInputBinding from explicit place-binding donors: placeEquiv,
  selected place, SourceImageRealization selected, fiberMonEquiv.

What is missing in the native root:
- no production declaration X.S -> SourceDefinition31Data.  The only native /
  contract bridge is the proposition NativeContractRecordBridge (an
  existential/equivalence gate), not a function.
- X.lattice has no index_equiv : family.index ≃ Int × Int.
- NativeC1 has the place bijection and selected bad place, but no
  SourceImageRealization selected and no fiberMonEquiv.

Therefore the named C10 bridge obligation is removed and replaced by the exact
missing donor interfaces plus a conditional no-go (empty contract supply).
No arbitrary V and no arbitrary selected R are introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C10BridgeProof

universe ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeClosure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.TargetSignature
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36

variable {l : PrimeGeFive}

/-- Exact missing OriginalInput donors for the native root. -/
structure NativeOriginalInputDonors (X : N8NativeInput l) where
  /-- The contract source datum; no native -> contract constructor exists. -/
  initial : SourceDefinition31Data.{0} l
  /-- Its arithmetic root must be the native arithmetic root. -/
  initial_arithmetic : initial.arithmetic = X.S.arithmetic
  /-- The theater-family index equivalence; NativeLattice does not carry it. -/
  index_equiv : X.family.index ≃ SourceTheorem311Index

/-- Construct OriginalInput from the explicit native donors. -/
noncomputable def nativeOriginalInputOfDonors
    (X : N8NativeInput l) (D : NativeOriginalInputDonors X) :
    OriginalInput l (NativePlaces X.S) where
  initial := D.initial
  family := X.family
  index_equiv := D.index_equiv
  arithmetic_alignment := by
    intro i
    rw [X.lattice.arithmetic_alignment i, ← D.initial_arithmetic]

/-- Exact missing place-binding donors for the old C1 SourceInputBinding. -/
structure NativePlaceBindingDonors
    (X : N8NativeInput l) (I : OriginalInput l (NativePlaces X.S)) where
  /-- Native place index bijection to the old place index. -/
  placeEquiv : NativePlaces X.S ≃
    NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)
  /-- Selected native place. -/
  selected : NativePlaces X.S
  /-- The selected realization R; not constructed by NativeC1. -/
  selected_realization : I.SourceImageRealization selected
  /-- Prime-strip fiber comparison; not constructed by NativeC1. -/
  fiberMonEquiv : ∀ (n m : Int) (v : NativePlaces X.S),
    (I.primeStripAt n m).Mon v ≃*
      SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (placeEquiv v)

/-- Construct the old C1 binding from explicit place-binding donors. -/
noncomputable def sourceInputBindingOfPlaceDonors
    (X : N8NativeInput l) (I : OriginalInput l (NativePlaces X.S))
    (P : NativePlaceBindingDonors X I) : SourceInputBinding I where
  place :=
    { placeEquiv := P.placeEquiv
      selected := P.selected
      selected_realization := P.selected_realization
      fiberMonEquiv := P.fiberMonEquiv }

/-- Conditional bridge construction from the exact missing donors. -/
noncomputable def nativeOldC1Bridge_of_donors
    (X : N8NativeInput l) (D : NativeOriginalInputDonors X)
    (P : NativePlaceBindingDonors X (nativeOriginalInputOfDonors X D)) :
    NativeOldC1Bridge X where
  input := nativeOriginalInputOfDonors X D
  binding := sourceInputBindingOfPlaceDonors X
    (nativeOriginalInputOfDonors X D) P

/-- Conditional no-go: if the tree supplies no SourceDefinition31Data at all,
then no NativeOldC1Bridge can exist. -/
theorem no_nativeOldC1Bridge_of_empty_contract
    (X : N8NativeInput l) (h : IsEmpty (SourceDefinition31Data.{0} l)) :
    IsEmpty (NativeOldC1Bridge X) := by
  refine ⟨fun B => h.false B.input.initial⟩

/-- Any native bridge forces the contract datum and the old C1 binding. -/
theorem nativeOldC1Bridge_requires_contract
    (X : N8NativeInput l) (B : NativeOldC1Bridge X) :
    Nonempty (SourceDefinition31Data.{0} l) :=
  ⟨B.input.initial⟩

end LeanFormal.IUT.N8Closure.C10BridgeProof
