import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4D9Supply
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31LocalValuationSections
import tmp.sheaf.n8.closure.NativeSourceSectionsCuspActual

/-!
# Native D7 intake from SourceCompletion clause E: construction attempt

Target: NativeD7Intake C = D7LocalGroupSectionSupply (canonical layer).

Actual source data available:
* C : SourceCompletion.{0} l;
* C.clauseE.finite_local / C.clauseE.infinite_local, indexed by the selected
  places {v : NumberFieldPlace C.arithmetic.K // v in C.sourceSignQuotientData.V};
* C.sourceSignQuotientData.V_section, V_eq_section, V_mod_bijection,
  V_place_comap;
* the canonical valuation section layer
  SourceValuationSectionLayer.canonical C.arithmetic with carriers
  {v // v in SourceArithmeticPrelude.canonical.selectedPlaces} and
  NumberFieldPlace C.arithmetic.Fmod.

Exact obstruction found in the actual data:
1. The canonical layer is constructed from
   SourceArithmeticPrelude.canonical C.arithmetic (the canonical restriction
   section), while clause E's selected set is
   C.sourceSignQuotientData.V = C.sourceSignQuotientData.V_section.selected.
   SourceCompletion carries only
   arithmeticPrelude_placeSection : C.arithmeticPrelude.placeSection =
   C.signQuotient.V_section, not an identification of the canonical restriction
   section with V_section. Therefore there is no source-level equivalence
   canonical.valuationCarrier ~ {v // v in C.sourceSignQuotientData.V}.
2. Clause E supplies local groups at the selected places, but its
   local_group_inclusion is a ProfiniteFundamentalGroupInclusion, not a
   bijection. D7LocalGroupSectionSupply requires a pointwise bijection
   localGroupSection x : localGroupCarrier x ~
   modifiedLocalGroupCarrier (sectionMap x). No such bijection is present in
   clause E or in the canonical layer.
3. Clause E place data propositions are attached to the selected finite/
   infinite local sources; D7 requires finitePlaceData/infinitePlaceData on the
   canonical place-section carrier. No transport across the missing comparison
   is provided.

Consequently no unconditional NativeD7Intake C is constructed. The exact
missing compatibility is isolated as ClauseEToD7Compatibility; the constructor
d7LocalGroupSectionSupplyOfCompatibility proves this compatibility is
sufficient. No local group or map is fabricated. No arbitrary constants,
degenerate placeholders, axioms, or unfilled proofs are introduced.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT
namespace InitialThetaSource
namespace Definition31D4D9Supply

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply
open LeanFormal.IUT.InitialThetaSource.NativeSourceSectionsCuspActual

variable {l : PrimeGeFive}

/-- The actual canonical valuation section layer of the completion. -/
noncomputable abbrev canonicalLayer (C : SourceCompletion.{0} l) :
    SourceValuationSectionLayer C.arithmetic :=
  SourceValuationSectionLayer.canonical C.arithmetic

/-- Exact missing compatibility between clause E selected-place local data and
the canonical D7 layer. Fields 1-2 are the missing place comparison; fields
3-5 are the missing pointwise local-group bijection and place data. -/
structure ClauseEToD7Compatibility (C : SourceCompletion.{0} l) where
  /-- Missing comparison: canonical selected carrier to clause-E selected set. -/
  placeEquiv :
    (canonicalLayer C).valuationCarrier ≃
      {v : NumberFieldPlace C.arithmetic.K //
        v ∈ C.sourceSignQuotientData.V}
  /-- The comparison is compatible with the canonical section map and the
  clause-E V_mod_bijection/V_place_comap at the restricted place. -/
  placeEquiv_comap :
    forall x : (canonicalLayer C).valuationCarrier,
      NumberFieldPlace.comap (k := C.arithmetic.Fmod) (placeEquiv x).1 =
        (canonicalLayer C).sectionMap x
  /-- Missing local-group carrier of X at each canonical place, transported
  from clause-E selected places via placeEquiv. -/
  localGroupCarrier : (canonicalLayer C).valuationCarrier -> Type
  /-- Missing local-group carrier of C at each modified place. -/
  modifiedLocalGroupCarrier :
    (canonicalLayer C).modifiedValuationCarrier -> Type
  /-- Missing pointwise bijective local-group section. This replaces the
  clause-E local_group_inclusion, which is only an inclusion. -/
  localGroupEquiv :
    forall x : (canonicalLayer C).valuationCarrier,
      localGroupCarrier x ≃
        modifiedLocalGroupCarrier ((canonicalLayer C).sectionMap x)
  /-- Missing finite-place data proposition on the canonical carrier. -/
  finitePlaceData : Prop
  finitePlaceData_proved : finitePlaceData
  /-- Missing infinite-place data proposition on the canonical carrier. -/
  infinitePlaceData : Prop
  infinitePlaceData_proved : infinitePlaceData

/-- Sufficient construction: the exact compatibility data yield the D7 local
group section supply for the canonical layer. -/
noncomputable def d7LocalGroupSectionSupplyOfCompatibility
    (C : SourceCompletion.{0} l) (H : ClauseEToD7Compatibility C) :
    D7LocalGroupSectionSupply.{0, 0} (canonicalLayer C) where
  localGroupCarrier := H.localGroupCarrier
  modifiedLocalGroupCarrier := H.modifiedLocalGroupCarrier
  localGroupSection := fun x => (H.localGroupEquiv x).toFun
  localGroupSection_injective := fun x => (H.localGroupEquiv x).injective
  localGroupSection_surjective := fun x => (H.localGroupEquiv x).surjective
  finitePlaceData := H.finitePlaceData
  finitePlaceData_proved := H.finitePlaceData_proved
  infinitePlaceData := H.infinitePlaceData
  infinitePlaceData_proved := H.infinitePlaceData_proved

/-- The D7 intake from the exact compatibility fields. -/
noncomputable def nativeD7IntakeOfCompatibility
    (C : SourceCompletion.{0} l) (H : ClauseEToD7Compatibility C) :
    NativeD7Intake C :=
  d7LocalGroupSectionSupplyOfCompatibility C H

theorem nativeD7Intake_nonempty_of_compatibility
    (C : SourceCompletion.{0} l) (H : ClauseEToD7Compatibility C) :
    Nonempty (NativeD7Intake C) :=
  ⟨nativeD7IntakeOfCompatibility C H⟩

/-- Exact obstruction statement: the existing SourceCompletion clause E does
not by itself provide the compatibility fields above. This is a statement of
the missing primitive fields, not a proof of non-existence. -/
def ClauseEToD7CompatibilityRequired (C : SourceCompletion.{0} l) : Prop :=
  Nonempty (ClauseEToD7Compatibility C)

/-- The canonical D7 gate reduces to the compatibility primitive. -/
theorem nativeD7Intake_nonempty_of_compatibility_required
    (C : SourceCompletion.{0} l) :
    Nonempty (ClauseEToD7Compatibility C) ->
      Nonempty (NativeD7Intake C) :=
  fun h => h.elim (fun H => nativeD7Intake_nonempty_of_compatibility C H)

end Definition31D4D9Supply
end InitialThetaSource
end LeanFormal.IUT

end
