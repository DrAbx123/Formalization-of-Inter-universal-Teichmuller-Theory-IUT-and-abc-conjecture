import tmp.sheaf.n8.closure.NativeBadFintypeSourceAttempt

/-!
# Native bad finite target correction

Corrected native input: NativeSourceWithBadFinite X adds the explicit field

  badFinite : X.S.tuple.source.V_mod_bad.Finite

to the native input.  This is the same kind of source-supplied finiteness as
D4D9Supply.badFinite : Fintype (Bad selection) in
SourceDefinition31D4D9Supply.lean:248.  It is not an arbitrary Fintype: it is
a source contract card that the old native S does not contain.

Old native SourceNativeInitialThetaData supplies V_mod_bad_nonempty and the
odd-residue condition only.  No production declaration proves
Set.Finite V_mod_bad from it.  Therefore old native S cannot produce the bad
Fintype; the finite proof is a genuine source input gap, and the correction
below records it explicitly.  Given that field, labels, compatibility and the
actual SourcePlacePartition are constructed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativeBadFiniteTargetCorrection

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.N8Closure.NativePartitionInputsActual
open LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source

variable {l : PrimeGeFive}

/-- Corrected native input: the old native input plus the explicit source
finiteness card for V_mod_bad. -/
structure NativeSourceWithBadFinite (X : N8NativeInput l) where
  badFinite : NativeBadSetFiniteSource X

/-- Build the corrected input from an explicit finite proof. -/
theorem nativeSourceWithBadFiniteOfSetFinite (X : N8NativeInput l)
    (h : NativeBadSetFiniteSource X) : NativeSourceWithBadFinite X :=
  ⟨h⟩

/-- The corrected input exists exactly when the source finiteness card is
supplied; this is the input gap, not a theorem about old native S. -/
theorem nativeSourceWithBadFinite_nonempty_iff
    (X : N8NativeInput l) :
    Nonempty (NativeSourceWithBadFinite X) ↔
      NativeBadSetFiniteSource X := by
  constructor
  · rintro ⟨C⟩
    exact C.badFinite
  · intro h
    exact ⟨nativeSourceWithBadFiniteOfSetFinite X h⟩

/-- Actual Fintype on native bad places from the corrected input. -/
@[reducible] def nativeSourceWithBadFiniteFintype
    (X : N8NativeInput l) (C : NativeSourceWithBadFinite X) :
    Fintype (NativeBadPlaces X) := by
  haveI : Finite (NativeBadPlaces X) := C.badFinite.to_subtype
  exact Fintype.ofFinite _

/-- Actual SourcePlacePartition from the corrected native input. -/
noncomputable def nativeSourceWithBadFinitePartition
    (X : N8NativeInput l) (C : NativeSourceWithBadFinite X) :
    SourcePlacePartition (NativeSelectedPlaces X) (NativeBadPlaces X) :=
  nativePartitionOfSourceFinite X C.badFinite

/-- Actual NativePartitionInputs from the corrected native input. -/
def nativeSourceWithBadFinitePartitionInputs
    (X : N8NativeInput l) (C : NativeSourceWithBadFinite X) :
    NativePartitionInputs X := by
  letI : Fintype (NativeBadPlaces X) :=
    nativeSourceWithBadFiniteFintype X C
  exact nativePartitionInputsOfFintype X

/-- The old native input alone is the uncorrected one; its only bad-set
existence data is Nonempty V_mod_bad.  The finite card is not derivable and is
therefore an explicit corrected-input field, not an arbitrary Fintype. -/
theorem oldNative_badFinite_is_sourceGap
    (X : N8NativeInput l) :
    NativeBadSetFiniteSource X ↔
      Nonempty (NativeSourceWithBadFinite X) :=
  (nativeSourceWithBadFinite_nonempty_iff X).symm

end LeanFormal.IUT.N8Closure.NativeBadFiniteTargetCorrection
