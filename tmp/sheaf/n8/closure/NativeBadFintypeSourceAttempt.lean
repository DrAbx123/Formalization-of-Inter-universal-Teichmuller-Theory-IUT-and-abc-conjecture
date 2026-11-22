import tmp.sheaf.n8.closure.NativePartitionInputsActual

/-!
# Native bad Fintype source attempt

Search result in production: no declaration supplies
Set.Finite V_mod_bad or Fintype (Bad P) from SourceNativeInitialThetaData.
The native source record only has V_mod_bad_nonempty and the odd-residue
condition.  Production instead supplies bad finiteness as a field:
- SourceDefinition31D4D9Supply.lean:248: D4D9Supply.badFinite :
  Fintype (Bad selection);
- SourcePlacePartitionReduction.lean:658: toSourcePlacePartition requires
  [Fintype (Bad P)] as an explicit hypothesis.

Actual result here: the exact source theorem needed is
Set.Finite X.S.tuple.source.V_mod_bad.  It is equivalent to
Nonempty (Fintype (NativeBadPlaces X)), and either one constructs the other
without choosing an arbitrary Fintype.  No production declaration currently
proves it.

No arbitrary Fintype is fabricated.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.N8Closure.NativePartitionInputsActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source

variable {l : PrimeGeFive}

/-- Exact source finiteness theorem needed for the native bad set. -/
def NativeBadSetFiniteSource (X : N8NativeInput l) : Prop :=
  X.S.tuple.source.V_mod_bad.Finite

/-- Actual: a finite bad set yields Fintype on the bad subtype. -/
theorem nativeBadFintype_of_sourceFinite
    (X : N8NativeInput l) (h : NativeBadSetFiniteSource X) :
    Nonempty (Fintype (NativeBadPlaces X)) := by
  haveI : Finite (NativeBadPlaces X) := h.to_subtype
  exact ⟨Fintype.ofFinite _⟩

/-- Actual converse: Fintype on the bad subtype yields a finite bad set. -/
theorem sourceFinite_of_nativeBadFintype
    (X : N8NativeInput l) (h : Fintype (NativeBadPlaces X)) :
    NativeBadSetFiniteSource X := by
  letI := h
  have hf : Set.Finite (Set.range (fun b : NativeBadPlaces X => b.1)) :=
    Set.finite_range _
  have hrange : Set.range (fun b : NativeBadPlaces X => b.1) =
      X.S.tuple.source.V_mod_bad := by
    ext p
    constructor
    · rintro ⟨b, rfl⟩
      exact b.2
    · intro hp
      exact ⟨⟨p, hp⟩, rfl⟩
  simpa [NativeBadSetFiniteSource, hrange] using hf

/-- Exact equivalence: the missing Fintype is precisely a finite proof for
the source bad set. -/
theorem nativeBadFintype_iff_sourceFinite (X : N8NativeInput l) :
    Nonempty (Fintype (NativeBadPlaces X)) ↔
      NativeBadSetFiniteSource X := by
  constructor
  · rintro ⟨h⟩
    exact sourceFinite_of_nativeBadFintype X h
  · intro h
    exact nativeBadFintype_of_sourceFinite X h

/-- The blocker restated as the exact required source theorem. -/
theorem nativePartitionFintypeGap_iff_sourceFinite (X : N8NativeInput l) :
    NativePartitionFintypeGap X ↔ NativeBadSetFiniteSource X :=
  nativeBadFintype_iff_sourceFinite X

/-- Actual partition from a supplied finite bad set; no Fintype is chosen. -/
def nativePartitionOfSourceFinite (X : N8NativeInput l)
    (h : NativeBadSetFiniteSource X) :
    SourcePlacePartition (NativeSelectedPlaces X) (NativeBadPlaces X) := by
  haveI : Finite (NativeBadPlaces X) := h.to_subtype
  letI : Fintype (NativeBadPlaces X) := Fintype.ofFinite _
  exact nativePartitionOfFintype X

end LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt
