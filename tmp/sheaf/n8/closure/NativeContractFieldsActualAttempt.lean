import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction
import tmp.sheaf.n8.closure.NativeC1

/-!
# Native contract fields actual attempt

Per-field attempt from a native SourceNativeInitialThetaData:
selectedPlaces, badPlaces, badIncluded, selectedNonempty, partition and
reduction attempts, then the torsion/orbicurve/sections/cusp and five
arithmetic compatibility fields.

Actual:
- nativeSelectedPlaces / nativeBadPlaces are the tuple source V and V_mod_bad
  subtypes;
- nativeBadIncluded is the actual V_mod_bijection on finite places;
- nativeSelectedNonempty follows from V_mod_bad_nonempty;
- nativePartitionFragment is the production fragment;
- SourcePlacePartition and SourceReductionClause are constructed from explicit
  exact missing inputs (fintype, labels, q/reduction data), not arbitrary.

Not actual (exact blockers):
- Fintype Bad, Nat labels and badLabel_compatible: not supplied by native data;
- qParameter/nonzero/contracting and reduction predicates/proofs: not supplied;
- torsion, orbicurve, sections, cusp: SourceNativeInitialThetaData supplies the
  six-tuple/clauses A-F, but no production constructor projects those to the
  contract clause records SourceTorsionClause, SourceOrbicurveClause,
  SourceSectionClause, SourceCuspClause;
- five arithmetic compatibility Propositions/proofs: no native definitions or
  proofs relate the arithmetic root to those contract clauses.

No arbitrary record is filled and no free Prop=True is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source

universe u

variable {l : PrimeGeFive}

/-- Actual selected-place carrier: the tuple source V subtype. -/
abbrev NativeSelectedPlaces (X : N8NativeInput l) : Type :=
  {v : NumberFieldPlace X.S.arithmetic.K // v ∈ X.S.tuple.source.V}

/-- Actual bad-place carrier: finite places in the tuple source V_mod_bad. -/
abbrev NativeBadPlaces (X : N8NativeInput l) : Type :=
  {p : NumberField.FinitePlace X.S.arithmetic.Fmod //
    p ∈ X.S.tuple.source.V_mod_bad}

/-- Actual bad inclusion, via the source V_mod_bijection. -/
def nativeBadIncluded (X : N8NativeInput l) :
    NativeBadPlaces X → NativeSelectedPlaces X :=
  fun b => X.S.tuple.source.V_mod_bijection (NumberFieldPlace.finite b.1)

theorem nativeSelectedNonempty (X : N8NativeInput l) :
    Nonempty (NativeSelectedPlaces X) := by
  rcases X.S.tuple.source.V_mod_bad_nonempty with ⟨p, _hp⟩
  exact ⟨X.S.tuple.source.V_mod_bijection (NumberFieldPlace.finite p)⟩

/-- Actual selected/bad data package; no missing field here. -/
structure NativeSelectedBadData (X : N8NativeInput l) where
  selectedPlaces : Type
  badPlaces : Type
  badIncluded : badPlaces → selectedPlaces
  selectedNonempty : Nonempty selectedPlaces

noncomputable def nativeSelectedBadData (X : N8NativeInput l) :
    NativeSelectedBadData X where
  selectedPlaces := NativeSelectedPlaces X
  badPlaces := NativeBadPlaces X
  badIncluded := nativeBadIncluded X
  selectedNonempty := nativeSelectedNonempty X

/-- Exact missing inputs for a SourcePlacePartition. -/
structure NativePartitionInputs (X : N8NativeInput l) where
  badFinite : Fintype (NativeBadPlaces X)
  selectedLabel : NativeSelectedPlaces X → Nat
  badLabel : NativeBadPlaces X → Nat
  badLabel_compatible : ∀ b,
    selectedLabel (nativeBadIncluded X b) = badLabel b

/-- Conditional actual partition from the exact missing inputs. -/
noncomputable def nativePartitionOfInputs (X : N8NativeInput l)
    (D : NativePartitionInputs X) :
    SourcePlacePartition (NativeSelectedPlaces X) (NativeBadPlaces X) where
  badIncluded := nativeBadIncluded X
  selectedNonempty := nativeSelectedNonempty X
  badFinite := D.badFinite
  selectedLabel := D.selectedLabel
  badLabel := D.badLabel
  badLabel_compatible := D.badLabel_compatible

/-- Exact missing inputs for a SourceReductionClause. -/
structure NativeReductionInputs (X : N8NativeInput l) where
  partition : NativePartitionInputs X
  stableReduction : NativeBadPlaces X → Prop
  stableReduction_proved : ∀ b, stableReduction b
  multiplicativeReduction : NativeBadPlaces X → Prop
  multiplicativeReduction_proved : ∀ b, multiplicativeReduction b
  splitMultiplicativeReduction : NativeBadPlaces X → Prop
  splitMultiplicativeReduction_proved : ∀ b, splitMultiplicativeReduction b
  reductionCompatibility : ∀ b,
    splitMultiplicativeReduction b → multiplicativeReduction b
  qParameter : NativeBadPlaces X → Real
  qParameter_nonzero : ∀ b, qParameter b ≠ 0
  qParameter_contracting : ∀ b, ‖qParameter b‖ < 1
  qParameter_reduction_compatibility : ∀ b,
    stableReduction b → qParameter b ≠ 1

/-- Conditional actual reduction clause from the exact missing inputs. -/
noncomputable def nativeReductionOfInputs (X : N8NativeInput l)
    (D : NativeReductionInputs X) :
    SourceReductionClause (NativeSelectedPlaces X) (NativeBadPlaces X) where
  partition := nativePartitionOfInputs X D.partition
  stableReduction := D.stableReduction
  stableReduction_proved := D.stableReduction_proved
  multiplicativeReduction := D.multiplicativeReduction
  multiplicativeReduction_proved := D.multiplicativeReduction_proved
  splitMultiplicativeReduction := D.splitMultiplicativeReduction
  splitMultiplicativeReduction_proved :=
    D.splitMultiplicativeReduction_proved
  reductionCompatibility := D.reductionCompatibility
  qParameter := D.qParameter
  qParameter_nonzero := D.qParameter_nonzero
  qParameter_contracting := D.qParameter_contracting
  qParameter_reduction_compatibility :=
    D.qParameter_reduction_compatibility

/-- Missing torsion clause target. -/
def NativeTorsionTarget (l : PrimeGeFive) : Prop :=
  Nonempty (SourceTorsionClause.{0, 0, 0} l)

/-- Missing orbicurve clause target. -/
def NativeOrbicurveTarget : Prop := Nonempty SourceOrbicurveClause.{0, 0, 0}

/-- Missing section clause target. -/
def NativeSectionsTarget : Prop := Nonempty SourceSectionClause.{0, 0, 0}

/-- Missing cusp clause target. -/
def NativeCuspTarget : Prop := Nonempty SourceCuspClause

/-- Exact missing five arithmetic compatibility package.  It is a target, not
an arbitrary filled record. -/
structure NativeArithmeticCompatibilityTarget where
  arithmetic_reduction_compatibility : Prop
  arithmetic_reduction_compatibility_proved :
    arithmetic_reduction_compatibility
  arithmetic_torsion_compatibility : Prop
  arithmetic_torsion_compatibility_proved : arithmetic_torsion_compatibility
  arithmetic_orbicurve_compatibility : Prop
  arithmetic_orbicurve_compatibility_proved :
    arithmetic_orbicurve_compatibility
  arithmetic_section_compatibility : Prop
  arithmetic_section_compatibility_proved : arithmetic_section_compatibility
  arithmetic_cusp_compatibility : Prop
  arithmetic_cusp_compatibility_proved : arithmetic_cusp_compatibility

/-- Production declaration gap list for the remaining contract fields.  This
is a record of the exact missing constructors, not a filled contract. -/
structure NativeContractProductionGap (X : N8NativeInput l) where
  partitionInputs_missing : NativePartitionInputs X → Prop
  reductionInputs_missing : NativeReductionInputs X → Prop
  torsionClause_missing : NativeTorsionTarget l
  orbicurveClause_missing : NativeOrbicurveTarget
  sectionsClause_missing : NativeSectionsTarget
  cuspClause_missing : NativeCuspTarget
  compatibility_missing : NativeArithmeticCompatibilityTarget → Prop

end LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
