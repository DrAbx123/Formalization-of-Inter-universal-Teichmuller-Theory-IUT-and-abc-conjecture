import tmp.sheaf.n8.closure.NativeInput
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import Mathlib.Tactic

/-!
# Native family index: actual attempt and exact gap

Task-507 asks for an actual equivalence

  X.family.index ≃ SourceTheorem311Index

or an actual NativeLattice whose index is Int × Int, from the native fields.

The minimal native root does not carry this datum.  NativeInput.NativeLattice has
exactly two fields:

  family : SourceHodgeTheaterFamily l (NativePlaces S)
  arithmetic_alignment : forall i, (family.theater i).arithmetic = S.arithmetic

SourceHodgeTheaterFamily.index is an arbitrary Type; there is no finite-type,
cardinality, Int × Int, or SourceTheorem311Index constraint in NativeLattice or
N8NativeInput.  Therefore no unconditional index equivalence can be constructed
from the root.  C10BridgeProof.lean records the same missing field as
NativeOriginalInputDonors.index_equiv; C6ConstructedBridge.lean records it as
C6IndexSupply (Nonempty (X.family.index ≃ SourceTheorem311Index)).

This file gives the exact missing datum, the conditional constructors, and the
precise claim that can be made.  The equivalence is an explicit parameter; it is
never manufactured by an arbitrary Equiv, Classical.choice, axiom, True, PUnit or
sorry.  No NativeLattice with Int × Int index is asserted unconditionally.
-/

noncomputable section
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.N8Closure.NativeInput

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

variable {l : PrimeGeFive}

/-! ## 1. The exact missing datum -/

/-- The precise index-equivalence datum missing from NativeLattice. -/
structure NativeIndexEquivData (X : N8NativeInput l) where
  index_equiv : X.family.index ≃ SourceTheorem311Index

/-- The missing datum as a proposition (the same shape as C6IndexSupply). -/
def MissingNativeIndexEquiv (X : N8NativeInput l) : Prop :=
  Nonempty (X.family.index ≃ SourceTheorem311Index)

/-- The conditional constructor: the equivalence is supplied, not derived. -/
noncomputable def nativeIndexEquivOfData
    (X : N8NativeInput l) (D : NativeIndexEquivData X) :
    X.family.index ≃ SourceTheorem311Index :=
  D.index_equiv

/-- The missing datum is exactly what the conditional constructor needs. -/
theorem nativeIndexEquivOfData_apply
    (X : N8NativeInput l) (D : NativeIndexEquivData X)
    (i : X.family.index) :
    nativeIndexEquivOfData X D i = D.index_equiv i := rfl

/-! ## 2. The conditional NativeLattice package -/

/-- A native lattice together with the explicit family index equivalence.  This
is the exact conditional package: the underlying NativeLattice is unchanged, and
no new arbitrary index equivalence is invented. -/
structure NativeLatticeWithIndex (X : N8NativeInput l) where
  lattice : NativeLattice X.S
  index_equiv : lattice.family.index ≃ SourceTheorem311Index

/-- Construct the conditional package from the native lattice and the supplied
index equivalence. -/
noncomputable def nativeLatticeWithIndex
    (X : N8NativeInput l) (e : X.family.index ≃ SourceTheorem311Index) :
    NativeLatticeWithIndex X where
  lattice := X.lattice
  index_equiv := e

/-- Construct the conditional package from the named missing datum. -/
noncomputable def nativeLatticeWithIndexOfData
    (X : N8NativeInput l) (D : NativeIndexEquivData X) :
    NativeLatticeWithIndex X :=
  nativeLatticeWithIndex X D.index_equiv

/-- The package's index equivalence is the supplied equivalence. -/
theorem nativeLatticeWithIndex_index_equiv
    (X : N8NativeInput l) (e : X.family.index ≃ SourceTheorem311Index) :
    (nativeLatticeWithIndex X e).index_equiv = e := rfl

/-- The package's lattice is the actual native lattice, unchanged. -/
theorem nativeLatticeWithIndex_lattice
    (X : N8NativeInput l) (e : X.family.index ≃ SourceTheorem311Index) :
    (nativeLatticeWithIndex X e).lattice = X.lattice := rfl

/-! ## 3. What is proved and what is missing -/

/-- The exact conditional consequence: an explicit index equivalence supplies a
native lattice-with-index package.  This is NOT an unconditional existence
theorem. -/
theorem nativeLatticeWithIndex_of_equiv
    (X : N8NativeInput l) (e : X.family.index ≃ SourceTheorem311Index) :
    Nonempty (NativeLatticeWithIndex X) :=
  ⟨nativeLatticeWithIndex X e⟩

/-- The missing datum expressed through the proposition. -/
theorem missingNativeIndexEquiv_iff
    (X : N8NativeInput l) :
    MissingNativeIndexEquiv X <->
      Nonempty (NativeIndexEquivData X) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨{ index_equiv := e }⟩
  · rintro ⟨D⟩
    exact ⟨D.index_equiv⟩

/-! ## 4. Exact gap statement

The native root has no field of type X.family.index ≃ SourceTheorem311Index.
The constructor above is conditional on NativeIndexEquivData; without that datum
the index type remains arbitrary and the Int × Int lattice cannot be produced.
No separate unconditional construction is asserted here.
-/

/-- The root-level gap: the minimal native lattice has no index equivalence. -/
def nativeIndexGap (X : N8NativeInput l) : Prop :=
  MissingNativeIndexEquiv X

end LeanFormal.IUT.N8Closure.NativeInput
