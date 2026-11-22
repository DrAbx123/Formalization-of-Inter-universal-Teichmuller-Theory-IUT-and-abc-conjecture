import tmp.sheaf.n8.closure.NativeContractFieldsActualAttempt
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction

/-!
# Native partition inputs actual attempt

Labels and compatibility are actual from the native residue-characteristic
data.  The only missing input is a Fintype instance on the native bad places.

Actual:
- nativeSelectedResidueLabel / nativeBadResidueLabel;
- nativeBadLabel_compatible (using tuple.source.V_place_comap and
  NumberFieldFinitePlace.residueCharacteristic_comap);
- nativePartitionInputsOfFintype X [Fintype (NativeBadPlaces X)]:
  NativePartitionInputs X;
- nativePartitionOfFintype X [Fintype ...]: actual SourcePlacePartition.

Decisive blocker:
- SourceNativeInitialThetaData supplies V_mod_bad_nonempty, odd residue
  characteristic, and the bijection, but no Fintype/Finite instance on
  V_mod_bad.  No production declaration gives Fintype (NativeBadPlaces X).
  That instance (or a finite bad-set proof) is exactly the missing production
  declaration.  Without it no NativePartitionInputs and no
  SourcePlacePartition can be formed.
- The Fintype is not fabricated and the labels are not arbitrary: they are
  residue characteristics.

No arbitrary Fintype/labels.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativePartitionInputsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source

variable {l : PrimeGeFive}

/-- Actual residue-characteristic label on selected places. -/
def nativeSelectedResidueLabel (X : N8NativeInput l) :
    NativeSelectedPlaces X → Nat :=
  fun v =>
    match v.1 with
    | NumberFieldPlace.finite p => NumberFieldFinitePlace.residueCharacteristic p
    | NumberFieldPlace.infinite _ => 0

/-- Actual residue-characteristic label on bad places. -/
def nativeBadResidueLabel (X : N8NativeInput l) :
    NativeBadPlaces X → Nat :=
  fun b => NumberFieldFinitePlace.residueCharacteristic b.1

/-- Actual label compatibility, from the native V_place_comap field. -/
theorem nativeBadLabel_compatible (X : N8NativeInput l) :
    ∀ b : NativeBadPlaces X,
      nativeSelectedResidueLabel X (nativeBadIncluded X b) =
        nativeBadResidueLabel X b := by
  intro b
  have hcomap := X.S.tuple.source.V_place_comap
    (X.S.tuple.source.V_mod_bijection (NumberFieldPlace.finite b.1))
  rw [Equiv.symm_apply_apply] at hcomap
  cases hv : (X.S.tuple.source.V_mod_bijection
      (NumberFieldPlace.finite b.1)).1 with
  | finite q =>
      have hq : NumberFieldFinitePlace.comap
          (k := X.S.arithmetic.Fmod) q = b.1 := by
        have h := hcomap
        rw [hv, NumberFieldPlace.comap_finite] at h
        injection h
      simp [nativeSelectedResidueLabel, nativeBadIncluded,
        nativeBadResidueLabel, hv]
      rw [← NumberFieldFinitePlace.residueCharacteristic_comap
        (k := X.S.arithmetic.Fmod) q, hq]
  | infinite w =>
      rw [hv, NumberFieldPlace.comap_infinite] at hcomap
      exact absurd hcomap (by simp)

/-- Conditional actual partition inputs: the only extra input is Fintype Bad. -/
def nativePartitionInputsOfFintype (X : N8NativeInput l)
    [badFinite : Fintype (NativeBadPlaces X)] :
    NativePartitionInputs X where
  badFinite := badFinite
  selectedLabel := nativeSelectedResidueLabel X
  badLabel := nativeBadResidueLabel X
  badLabel_compatible := nativeBadLabel_compatible X

/-- Conditional actual SourcePlacePartition, once the missing Fintype is
supplied. -/
def nativePartitionOfFintype (X : N8NativeInput l)
    [Fintype (NativeBadPlaces X)] :
    SourcePlacePartition (NativeSelectedPlaces X) (NativeBadPlaces X) :=
  nativePartitionOfInputs X (nativePartitionInputsOfFintype X)

/-- Exact missing production declaration: a Fintype instance on native bad
places (equivalently, a finite proof for the tuple source V_mod_bad). -/
def NativePartitionFintypeGap (X : N8NativeInput l) : Prop :=
  Nonempty (Fintype (NativeBadPlaces X))

/-- Any actual NativePartitionInputs necessarily contains the missing Fintype. -/
theorem nativePartitionInputs_implies_fintype
    (X : N8NativeInput l) (D : NativePartitionInputs X) :
    NativePartitionFintypeGap X :=
  ⟨D.badFinite⟩

/-- Fintype gap is necessary: without it, NativePartitionInputs cannot be
formed.  This is the decisive blocker; no Fintype is fabricated. -/
theorem nativePartitionInputs_of_fintype_iff
    (X : N8NativeInput l) :
    NativePartitionFintypeGap X →
      Nonempty (NativePartitionInputs X) := by
  rintro ⟨h⟩
  exact ⟨nativePartitionInputsOfFintype X⟩

end LeanFormal.IUT.N8Closure.NativePartitionInputsActual
