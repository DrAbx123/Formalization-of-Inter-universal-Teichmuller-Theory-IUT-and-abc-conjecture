import tmp.sheaf.xif.paper.S432SmallModelActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S456RationalInclusionActual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S432SmallModelActual

universe u
variable {K : Type u} [Field K]

noncomputable abbrev coverField (X : Example32SmallBase K) : Type u :=
  (ULiftHom.objDown X).unop.obj.obj

noncomputable instance coverFieldField (X : Example32SmallBase K) :
    Field (coverField X) :=
  ((ULiftHom.objDown X).unop.property).toField

noncomputable def arrowAlgebraMap {X Y : Example32SmallBase K} (f : X ⟶ Y) :
    coverField Y →ₐ[K] coverField X :=
  (f.down.unop).hom.hom.hom

noncomputable def unitInclusionPullback {X Y : Example32SmallBase K} (f : X ⟶ Y) :
    (coverField Y)ˣ →* (coverField X)ˣ :=
  Units.map (arrowAlgebraMap f).toMonoidHom

theorem unitInclusionPullback_injective {X Y : Example32SmallBase K} (f : X ⟶ Y) :
    Function.Injective (unitInclusionPullback f) := by
  intro x y h
  apply Units.ext
  have hval := congrArg (fun z : (coverField X)ˣ => (z : coverField X)) h
  change (arrowAlgebraMap f) (x : coverField Y) =
    (arrowAlgebraMap f) (y : coverField Y) at hval
  exact RingHom.injective (arrowAlgebraMap f).toRingHom hval

def Example32IsFSM {X Y : Example32SmallBase K} (f : X ⟶ Y) : Prop :=
  Function.Bijective (unitInclusionPullback f)

end LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
end
