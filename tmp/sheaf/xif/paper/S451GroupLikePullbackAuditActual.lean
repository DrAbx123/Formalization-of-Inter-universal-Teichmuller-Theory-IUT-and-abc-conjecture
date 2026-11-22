import tmp.sheaf.xif.paper.S442DvCoverNormPullbackActual
import tmp.sheaf.xif.paper.S432SmallModelActual

/-! # S451 audit: GroupLikeAddMonoidOn pullback must be constructible/injective

GroupLikeAddMonoidOn.pullback must be injective and, for IsFSM arrows, bijective.
The norm pullback Algebra.norm L : L'^× -> L^× is generally not injective
(norm-one units can be nontrivial), so it cannot be rationalFunctions.pullback.

The correct direction is the opposite-category algebra inclusion
L_Y^× -> L_X^× via Units.map of the field algebra map; it is injective.
A surjectivity/bijectivity on every arrow still requires the IsFSM predicate to
be restricted (S432 currently uses IsFSM := fun _ => True, which would demand
bijectivity on every cover arrow).  No fake norm/pullback is asserted. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S451GroupLikePullbackAuditActual

open CategoryTheory

universe u

/-- Units.map is injective when the underlying monoid hom is injective. -/
theorem unitsMap_injective {M N : Type u} [Monoid M] [Monoid N]
    (f : M →* N) (hf : Function.Injective f) :
    Function.Injective (Units.map f) := by
  intro x y hxy
  apply Units.ext
  exact hf (congrArg Units.val hxy)

/-- Exact missing datum for the inclusion pullback: a choice of the
opposite-category algebra map and proof that the induced Units.map is
bijective on every IsFSM arrow. -/
structure InclusionPullbackBijectiveData
    {D : Type u} [Category.{u} D]
    (obj : D → Type u) [∀ X, Monoid (obj X)]
    (IsFSMArrow : ∀ {X Y : D}, (X ⟶ Y) → Prop) where
  pullback : ∀ {X Y : D}, (X ⟶ Y) → obj Y →* obj X
  pullback_injective : ∀ {X Y} (f : X ⟶ Y), Function.Injective (pullback f)
  fsm_bijective : ∀ {X Y} (f : X ⟶ Y), IsFSMArrow f → Function.Bijective (pullback f)

end LeanFormal.IUT.XiFPaper.S451GroupLikePullbackAuditActual

end
