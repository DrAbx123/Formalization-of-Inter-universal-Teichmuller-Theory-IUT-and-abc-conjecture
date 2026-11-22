import tmp.sheaf.xif.paper.ClauseEToD7Actual

/-!
# Clause E -> D7 local-group data: actual finite/infinite data and the
# exact missing pointwise bijection

The place part of ClauseEToD7Compatibility is constructed in
ClauseEToD7Actual. This file constructs the finite/infinite place data from
the actual SourceClauseE local sources:

* for every canonical place x and finite witness hx, use
  C.clauseE.finite_local (clauseEPlaceEquiv C x) hx;
* for every infinite witness hx, use C.clauseE.infinite_local.

The only remaining local-group object is the pointwise bijection
  localGroupCarrier x ~= modifiedLocalGroupCarrier (sectionMap x).
Clause E supplies only local_group_inclusion (an inclusion), not this
bijection. The exact missing package is isolated as
ClauseEToD7LocalGroupBijection; no arbitrary group carrier or map is chosen.

No toy/True/PUnit/axiom/sorry is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper
namespace ClauseEToD7LocalGroupActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.ClauseEToD7Actual

universe u

variable {l : PrimeGeFive}
variable (C : SourceCompletion.{0} l)

/-- The actual canonical valuation-section layer. -/
abbrev canonicalLayer : SourceValuationSectionLayer C.arithmetic :=
  SourceValuationSectionLayer.canonical C.arithmetic

/-- Actual finite-place data: every finite selected place has the clause-E
finite local source. -/
def finitePlaceData (C : SourceCompletion.{0} l) : Prop :=
  forall (x : (canonicalLayer C).valuationCarrier)
    (hx : (clauseEPlaceEquiv C x).1.IsFinite),
      Nonempty
        (SourceFiniteLocalSource C.arithmetic C.sourceSignQuotientData
          C.clauseA C.clauseB C.clauseC C.clauseD
          (selectedFinitePlace (v := (clauseEPlaceEquiv C x).1) hx))

/-- Actual finite-place data is inhabited from the clause-E finite local
source. -/
theorem finitePlaceData_proved : finitePlaceData C := by
  intro x hx
  exact ⟨C.clauseE.finite_local (clauseEPlaceEquiv C x) hx⟩

/-- Actual infinite-place data: every infinite selected place has the
clause-E infinite local source. -/
def infinitePlaceData (C : SourceCompletion.{0} l) : Prop :=
  forall (x : (canonicalLayer C).valuationCarrier)
    (hx : (clauseEPlaceEquiv C x).1.IsInfinite),
      Nonempty
        (SourceInfiniteLocalSource C.arithmetic C.sourceSignQuotientData
          C.clauseA C.clauseB C.clauseC C.clauseD
          (selectedInfinitePlace (v := (clauseEPlaceEquiv C x).1) hx))

/-- Actual infinite-place data is inhabited from the clause-E infinite local
source. -/
theorem infinitePlaceData_proved : infinitePlaceData C := by
  intro x hx
  exact ⟨C.clauseE.infinite_local (clauseEPlaceEquiv C x) hx⟩

/-- Exact missing local-group carriers and pointwise bijection. -/
structure ClauseEToD7LocalGroupBijection where
  localGroupCarrier : (canonicalLayer C).valuationCarrier -> Type
  modifiedLocalGroupCarrier :
    (canonicalLayer C).modifiedValuationCarrier -> Type
  localGroupEquiv :
    forall x : (canonicalLayer C).valuationCarrier,
      localGroupCarrier x ≃
        modifiedLocalGroupCarrier ((canonicalLayer C).sectionMap x)

/-- Exact missing local-group package. -/
def MissingClauseEToD7LocalGroupBijection : Prop :=
  Nonempty (ClauseEToD7LocalGroupBijection C)

/-- Actual ClauseEToD7LocalGroupData from the exact pointwise bijection and
the actual finite/infinite place data. -/
noncomputable def localGroupData_of_bijection
    (B : ClauseEToD7LocalGroupBijection C) :
    ClauseEToD7LocalGroupData C where
  localGroupCarrier := B.localGroupCarrier
  modifiedLocalGroupCarrier := B.modifiedLocalGroupCarrier
  localGroupEquiv := B.localGroupEquiv
  finitePlaceData := finitePlaceData C
  finitePlaceData_proved := finitePlaceData_proved C
  infinitePlaceData := infinitePlaceData C
  infinitePlaceData_proved := infinitePlaceData_proved C

/-- Every ClauseEToD7LocalGroupData gives the exact pointwise bijection. -/
noncomputable def bijection_of_localGroupData
    (D : ClauseEToD7LocalGroupData C) :
    ClauseEToD7LocalGroupBijection C where
  localGroupCarrier := D.localGroupCarrier
  modifiedLocalGroupCarrier := D.modifiedLocalGroupCarrier
  localGroupEquiv := D.localGroupEquiv

/-- The exact reduction: local-group data exists iff the pointwise bijection
exists. The finite/infinite data are actual. -/
theorem localGroupData_nonempty_iff_bijection :
    Nonempty (ClauseEToD7LocalGroupData C) ↔
      MissingClauseEToD7LocalGroupBijection C := by
  constructor
  · rintro ⟨D⟩
    exact ⟨bijection_of_localGroupData C D⟩
  · rintro ⟨B⟩
    exact ⟨localGroupData_of_bijection C B⟩

/-- Exact status: finite/infinite place data are constructed; the only missing
object is the pointwise local-group bijection. -/
theorem clauseEToD7LocalGroup_status :
    finitePlaceData C ∧ infinitePlaceData C ∧
      (Nonempty (ClauseEToD7LocalGroupData C) ↔
        MissingClauseEToD7LocalGroupBijection C) :=
  ⟨finitePlaceData_proved C, infinitePlaceData_proved C,
    localGroupData_nonempty_iff_bijection C⟩

end ClauseEToD7LocalGroupActual
end LeanFormal.IUT.XiFPaper
end
