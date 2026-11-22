import Iut.Foundations.SourceModelFrobenioidFactorization

/-! # Model factorization pullback does not use base categorical pullbacks

SourceModelFrobenioid.Carrier.factorization builds the Definition 1.3(iv)
pullback arrow from the model fields alone:

* pullbackObject target arrow.base has base = the domain of arrow.base and
  divisorClass = gpPullback arrow.base target.divisorClass;
* pullbackArrow has rationalFunction = 0, divisor = 0, base = arrow.base;
* pullbackArrow_isPullback proves IsPullback using only Hom fields.

No categorical pullback/fiber product in D is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.SourceModelFactorizationNoBasePullbackActual

open CategoryTheory
open Iut.SourceModelFrobenioid
open Iut.SourceModelFrobenioid.Carrier

universe u

variable {D : Type u} [Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : Iut.DivisorialMonoidOn D IsFSM}
variable {data : Input Phi}

/-- The canonical factorization's pullback arrow is literally pullbackArrow
over arrow.base. -/
theorem factorization_pullback_eq_pullbackArrow
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    (factorization arrow).pullback =
      pullbackArrow Phi data target arrow.base := rfl

/-- The canonical factorization's pullback has the model IsPullback proof,
constructed from pullbackArrow_isPullback, not from a base-category pullback. -/
theorem factorization_pullback_isPullback
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    (preFrobenioid Phi data).IsPullback (factorization arrow).pullback :=
  (factorization arrow).pullback_type

/-- The same IsPullback proof as a direct re-export of the model theorem. -/
theorem factorization_pullback_isPullback_via_model
    {source target : Carrier Phi data} (arrow : source ⟶ target) :
    (preFrobenioid Phi data).IsPullback (factorization arrow).pullback := by
  rw [factorization_pullback_eq_pullbackArrow]
  exact pullbackArrow_isPullback Phi data target arrow.base

end LeanFormal.IUT.XiFPaper.SourceModelFactorizationNoBasePullbackActual

end
