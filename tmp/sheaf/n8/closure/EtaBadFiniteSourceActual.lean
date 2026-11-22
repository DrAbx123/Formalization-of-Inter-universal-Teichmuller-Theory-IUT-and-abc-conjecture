import tmp.sheaf.n8.closure.NativeBadFiniteTargetCorrection

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Native bad-set finiteness source attempt

Native Clause data supplies only `V_mod_bad_nonempty` and the odd-residue
condition.  Neither implies `Set.Finite V_mod_bad`: `V_mod_bad` is an
arbitrary source subset of the finite places of Fmod, so it could be infinite
within the class of odd-residue places.  No production declaration proves the
finite card.  This file records the exact required source condition and its
equivalence to the corrected native input; no arbitrary finite witness or
Fintype is fabricated.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt
open LeanFormal.IUT.N8Closure.NativeBadFiniteTargetCorrection
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt

namespace LeanFormal.IUT.N8Closure.EtaBadFiniteSourceActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Exact source finiteness condition required for the bad set. -/
def RequiredBadFiniteness : Prop :=
  NativeBadSetFiniteSource X

/-- Actual equivalence: the corrected native input exists exactly when the
source finiteness condition is supplied. -/
theorem nativeSourceWithBadFinite_iff_required :
    Nonempty (NativeSourceWithBadFinite X) ↔ RequiredBadFiniteness (X := X) :=
  nativeSourceWithBadFinite_nonempty_iff X

/-- Actual construction of the corrected input from the exact source card. -/
theorem nativeSourceWithBadFinite_of_required
    (h : RequiredBadFiniteness (X := X)) :
    Nonempty (NativeSourceWithBadFinite X) :=
  (nativeSourceWithBadFinite_iff_required (X := X)).mpr h

/-- The actual partition follows from the exact source card; no arbitrary
Fintype is introduced. -/
noncomputable def nativePartitionOfRequired
    (h : RequiredBadFiniteness (X := X)) :
    SourcePlacePartition (NativeSelectedPlaces X) (NativeBadPlaces X) :=
  nativePartitionOfSourceFinite X h

/-- Exact gap: the required source finiteness is not a theorem of the old
native input; it has to be supplied as the source card. -/
def BadFinitenessSourceGap : Prop :=
  ¬ Nonempty (NativeSourceWithBadFinite X)

end LeanFormal.IUT.N8Closure.EtaBadFiniteSourceActual

end