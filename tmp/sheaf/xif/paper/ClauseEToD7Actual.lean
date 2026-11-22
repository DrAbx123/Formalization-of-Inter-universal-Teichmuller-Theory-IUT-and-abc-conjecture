import tmp.sheaf.n8.closure.NativeD7Proof
import tmp.sheaf.n8.closure.NativeSourceSectionsCuspActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31LocalValuationSections

/-!
# Clause E -> D7 compatibility: actual place part and exact local-group gap

The D7 compatibility structure (NativeD7Proof.ClauseEToD7Compatibility) has:
* placeEquiv between the canonical valuation carrier and the clause-E selected
  places;
* placeEquiv_comap against the canonical section map;
* local-group carrier/equivalence and finite/infinite place data.

This file constructs the place part ACTUALLY, without any missing comparison:
the canonical layer sectionMap is a bijection onto Fmod places, and the
SourceSignQuotientData V_mod_bijection is a bijection from Fmod places onto
the clause-E selected places. Their composite gives placeEquiv; the comap law
uses V_place_comap.

The remaining local-group/finite-place package is isolated exactly; Clause E
only supplies a profinite inclusion, not the pointwise bijection required by
D7. No local group, bijection, or place data is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper
namespace ClauseEToD7Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply

universe u

variable {l : PrimeGeFive}
variable (C : SourceCompletion.{0} l)

/-- The actual canonical valuation-section layer. -/
noncomputable abbrev canonicalLayer : SourceValuationSectionLayer C.arithmetic :=
  SourceValuationSectionLayer.canonical C.arithmetic

/-- The canonical section map as an equivalence between the canonical and
modified valuation carriers. -/
noncomputable def canonicalSectionEquiv :
    (canonicalLayer C).valuationCarrier ≃
      (canonicalLayer C).modifiedValuationCarrier where
  toFun := (canonicalLayer C).sectionMap
  invFun := (canonicalLayer C).sectionRightInverse
  left_inv := (canonicalLayer C).section_left_inverse
  right_inv := (canonicalLayer C).section_right_inverse

/-- Actual place equivalence: canonical valuation carriers are Fmod places,
and the source V_mod_bijection identifies Fmod places with the clause-E
selected places. -/
noncomputable def clauseEPlaceEquiv :
    (canonicalLayer C).valuationCarrier ≃
      {v : NumberFieldPlace C.arithmetic.K //
        v ∈ C.sourceSignQuotientData.V} :=
  (canonicalSectionEquiv C).trans C.sourceSignQuotientData.V_mod_bijection

/-- The actual place equivalence commutes with the canonical section map and
the source comap map. -/
theorem clauseEPlaceEquiv_comap
    (x : (canonicalLayer C).valuationCarrier) :
    NumberFieldPlace.comap (k := C.arithmetic.Fmod)
        (clauseEPlaceEquiv C x).1 =
      (canonicalLayer C).sectionMap x := by
  change NumberFieldPlace.comap (k := C.arithmetic.Fmod)
      ((C.sourceSignQuotientData.V_mod_bijection)
        ((canonicalSectionEquiv C) x)).1 =
    (canonicalSectionEquiv C) x
  rw [C.sourceSignQuotientData.V_place_comap]
  exact Equiv.symm_apply_apply _ _

/-- The actual place half of the D7 compatibility. -/
structure ClauseEToD7PlaceData where
  placeEquiv :
    (canonicalLayer C).valuationCarrier ≃
      {v : NumberFieldPlace C.arithmetic.K //
        v ∈ C.sourceSignQuotientData.V}
  placeEquiv_comap :
    forall x : (canonicalLayer C).valuationCarrier,
      NumberFieldPlace.comap (k := C.arithmetic.Fmod)
          (placeEquiv x).1 =
        (canonicalLayer C).sectionMap x

/-- The actual place data, constructed unconditionally. -/
noncomputable def clauseEToD7PlaceData : ClauseEToD7PlaceData C where
  placeEquiv := clauseEPlaceEquiv C
  placeEquiv_comap := clauseEPlaceEquiv_comap C

/-- The exact remaining local-group data of D7. Clause E supplies local group
data at selected places only through a profinite inclusion, not the pointwise
bijection below. -/
structure ClauseEToD7LocalGroupData where
  localGroupCarrier : (canonicalLayer C).valuationCarrier -> Type
  modifiedLocalGroupCarrier :
    (canonicalLayer C).modifiedValuationCarrier -> Type
  localGroupEquiv :
    forall x : (canonicalLayer C).valuationCarrier,
      localGroupCarrier x ≃
        modifiedLocalGroupCarrier ((canonicalLayer C).sectionMap x)
  finitePlaceData : Prop
  finitePlaceData_proved : finitePlaceData
  infinitePlaceData : Prop
  infinitePlaceData_proved : infinitePlaceData

/-- The exact missing local-group package. -/
def MissingClauseEToD7LocalGroupData : Prop :=
  Nonempty (ClauseEToD7LocalGroupData C)

/-- Full D7 compatibility from the actual place part and the exact local-group
package. -/
noncomputable def clauseEToD7Compatibility_of_localGroupData
    (H : ClauseEToD7LocalGroupData C) :
    ClauseEToD7Compatibility C where
  placeEquiv := clauseEPlaceEquiv C
  placeEquiv_comap := clauseEPlaceEquiv_comap C
  localGroupCarrier := H.localGroupCarrier
  modifiedLocalGroupCarrier := H.modifiedLocalGroupCarrier
  localGroupEquiv := H.localGroupEquiv
  finitePlaceData := H.finitePlaceData
  finitePlaceData_proved := H.finitePlaceData_proved
  infinitePlaceData := H.infinitePlaceData
  infinitePlaceData_proved := H.infinitePlaceData_proved

/-- Every full D7 compatibility gives the local-group package (the place part
is discarded). -/
def localGroupData_of_clauseEToD7Compatibility
    (H : ClauseEToD7Compatibility C) : ClauseEToD7LocalGroupData C where
  localGroupCarrier := H.localGroupCarrier
  modifiedLocalGroupCarrier := H.modifiedLocalGroupCarrier
  localGroupEquiv := H.localGroupEquiv
  finitePlaceData := H.finitePlaceData
  finitePlaceData_proved := H.finitePlaceData_proved
  infinitePlaceData := H.infinitePlaceData
  infinitePlaceData_proved := H.infinitePlaceData_proved

/-- The exact reduction: full Clause E -> D7 compatibility is equivalent to
the local-group package, since the place part is constructed unconditionally. -/
theorem clauseEToD7Compatibility_nonempty_iff :
    Nonempty (ClauseEToD7Compatibility C) ↔
      MissingClauseEToD7LocalGroupData C := by
  constructor
  · rintro ⟨H⟩
    exact ⟨localGroupData_of_clauseEToD7Compatibility C H⟩
  · rintro ⟨H⟩
    exact ⟨clauseEToD7Compatibility_of_localGroupData C H⟩

/-- Exact status: the place comparison is actual; the local-group/finite-place
data is the only missing part. -/
theorem clauseEToD7_status :
    Nonempty (ClauseEToD7PlaceData C) ∧
      (Nonempty (ClauseEToD7Compatibility C) ↔
        MissingClauseEToD7LocalGroupData C) :=
  ⟨⟨clauseEToD7PlaceData C⟩, clauseEToD7Compatibility_nonempty_iff C⟩

end ClauseEToD7Actual
end LeanFormal.IUT.XiFPaper
end
