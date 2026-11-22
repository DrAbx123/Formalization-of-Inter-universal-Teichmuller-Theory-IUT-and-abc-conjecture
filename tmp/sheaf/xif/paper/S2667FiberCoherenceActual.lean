import tmp.sheaf.xif.paper.S2619ActionGroupoidFiberSkeleton
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

noncomputable section
open CategoryTheory
open Iut
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S2667: the actual fiber pseudofunctor

For an action groupoid datum `D` on `Iut.SchemeOverField F`, S2619 constructs
the fiber categories `S2619FiberAt D V` (the action groupoid of the
`S2619G l`-action on `V.unop ⟶ D.U`) and pullback functors
`S2619PullFunctor D h : S2619FiberAt D V ⥤ S2619FiberAt D V'` for `h : V ⟶ V'`.

In this file we assemble these data into an actual pseudofunctor

`S2667FiberPseudofunctor D : LocallyDiscrete (SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{0,u}`

with `obj := S2619FiberAt D` and `map := S2619PullFunctor D`.  The source is
locally discrete, so a pseudofunctor out of it is the same as a strict functor
of the underlying categories; we build the strict functor and use
`CategoryTheory.Functor.toPseudofunctor'`.

The only nontrivial point is that `S2619PullFunctor` is only *weakly*
functorial (its object part composes up to associativity).  We prove the two
functor equalities `S2619PullFunctor (𝟙 V) = 𝟭 _` and
`S2619PullFunctor (f ≫ g) = S2619PullFunctor f ⋙ S2619PullFunctor g`
using `CategoryTheory.Functor.hext`, which asks for heterogeneous equalities of
morphisms instead of the `eqToHom`-twisted formulation of
`CategoryTheory.Functor.ext`.  Values of morphisms in the action groupoid
make these heterogeneous equalities immediate.
-/

namespace LeanFormal.IUT.XiFPaper.S2667FiberCoherenceActual

universe u
variable (l : LeanFormal.IUT.PrimeGeFive) (F : Type u) [CommRing F]
variable (D : LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton.S2619ActionGroupoidData l F)

open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton

/-- The fiber of `S2619FiberAt` as a plain (unbundled) category, which is
definitionally the underlying category of the bundled `Cat` object. -/
abbrev S2667FiberCat (V : (Iut.SchemeOverField F)ᵒᵖ) : Type u :=
  ActionCategory (S2619G l) (S2619Hom l F D V)

/-- The S2619 pullback functor, viewed as a functor between the unbundled
fiber categories. -/
def S2667Pull {V V' : (Iut.SchemeOverField F)ᵒᵖ} (h : V ⟶ V') :
    S2667FiberCat l F D V ⥤ S2667FiberCat l F D V' :=
  S2619PullFunctor l F D h

lemma S2667Pull_obj_id (V : (Iut.SchemeOverField F)ᵒᵖ) (X : S2667FiberCat l F D V) :
    (S2667Pull l F D (𝟙 V)).obj X = X := by
  rcases X with ⟨c, a⟩
  cases c
  refine Sigma.ext ?_ ?_
  · exact Subsingleton.elim _ _
  · exact heq_of_eq (by simp [S2667Pull, S2619PullFunctor])

lemma S2667Pull_map_id (V : (Iut.SchemeOverField F)ᵒᵖ) (X Y : S2667FiberCat l F D V)
    (f : X ⟶ Y) :
    (S2667Pull l F D (𝟙 V)).map f ≍ f := by
  rcases X with ⟨cx, ax⟩
  cases cx
  rcases Y with ⟨cy, ay⟩
  cases cy
  rcases f with ⟨m, hm⟩
  refine (Subtype.heq_iff_coe_eq ?_).2 ?_
  · intro x
    simp only [S2667Pull, S2619PullFunctor]
    exact Iff.rfl
  · rfl

lemma S2667Pull_obj_comp {V V' V'' : (Iut.SchemeOverField F)ᵒᵖ} (f : V ⟶ V') (g : V' ⟶ V'')
    (X : S2667FiberCat l F D V) :
    (S2667Pull l F D (f ≫ g)).obj X =
      (S2667Pull l F D f ⋙ S2667Pull l F D g).obj X := by
  rcases X with ⟨c, a⟩
  cases c
  refine Sigma.ext ?_ ?_
  · exact Subsingleton.elim _ _
  · change HEq ((f ≫ g).unop ≫ a) (g.unop ≫ f.unop ≫ a)
    exact heq_of_eq (Category.assoc g.unop f.unop a)

lemma S2667Pull_map_comp {V V' V'' : (Iut.SchemeOverField F)ᵒᵖ} (f : V ⟶ V') (g : V' ⟶ V'')
    (X Y : S2667FiberCat l F D V) (h : X ⟶ Y) :
    (S2667Pull l F D (f ≫ g)).map h ≍
      (S2667Pull l F D f ⋙ S2667Pull l F D g).map h := by
  rcases X with ⟨cx, ax⟩
  cases cx
  rcases Y with ⟨cy, ay⟩
  cases cy
  rcases h with ⟨m, hm⟩
  refine (Subtype.heq_iff_coe_eq ?_).2 ?_
  · intro x
    rw [S2667Pull_obj_comp l F D f g ⟨PUnit.unit, ax⟩,
      S2667Pull_obj_comp l F D f g ⟨PUnit.unit, ay⟩]
  · rfl

lemma S2667Pull_id (V : (Iut.SchemeOverField F)ᵒᵖ) :
    S2667Pull l F D (𝟙 V) = 𝟭 (S2667FiberCat l F D V) :=
  CategoryTheory.Functor.hext (S2667Pull_obj_id l F D V) (S2667Pull_map_id l F D V)

lemma S2667Pull_comp {V V' V'' : (Iut.SchemeOverField F)ᵒᵖ} (f : V ⟶ V') (g : V' ⟶ V'') :
    S2667Pull l F D (f ≫ g) =
      S2667Pull l F D f ⋙ S2667Pull l F D g :=
  CategoryTheory.Functor.hext (S2667Pull_obj_comp l F D f g) (S2667Pull_map_comp l F D f g)

/-- The pullback functors of S2619 are strictly unital. -/
theorem S2667PullFunctor_id (V : (Iut.SchemeOverField F)ᵒᵖ) :
    S2619PullFunctor l F D (𝟙 V) = 𝟭 (S2619FiberAt l F D V) :=
  S2667Pull_id l F D V

/-- The pullback functors of S2619 are strictly composition compatible. -/
theorem S2667PullFunctor_comp {V V' V'' : (Iut.SchemeOverField F)ᵒᵖ} (f : V ⟶ V')
    (g : V' ⟶ V'') :
    S2619PullFunctor l F D (f ≫ g) =
      S2619PullFunctor l F D f ⋙ S2619PullFunctor l F D g :=
  S2667Pull_comp l F D f g

/-- The strict functor of categories underlying the fiber pseudofunctor. -/
def S2667FiberFunctor : (Iut.SchemeOverField F)ᵒᵖ ⥤ Cat.{0, u} where
  obj V := S2619FiberAt l F D V
  map h := (S2619PullFunctor l F D h).toCatHom
  map_id V := CategoryTheory.Cat.Hom.ext (S2667PullFunctor_id l F D V)
  map_comp f g := CategoryTheory.Cat.Hom.ext (S2667PullFunctor_comp l F D f g)

/-- The actual pseudofunctor sending `V` to the action-groupoid fiber
`S2619FiberAt D V` and `h` to the pullback functor `S2619PullFunctor D h`. -/
def S2667FiberPseudofunctor :
    LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{0, u} :=
  (S2667FiberFunctor l F D).toPseudofunctor'

/-- The object part of `S2667FiberPseudofunctor` is `S2619FiberAt`. -/
theorem S2667Fiber_obj (V : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) :
    (S2667FiberPseudofunctor l F D).obj V = S2619FiberAt l F D V.as := rfl

/-- The morphism part of `S2667FiberPseudofunctor` is `S2619PullFunctor`. -/
theorem S2667Fiber_map {V V' : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (f : V ⟶ V') :
    (S2667FiberPseudofunctor l F D).map f =
      (S2619PullFunctor l F D f.as).toCatHom := rfl

/-- The unit coherence of `S2667FiberPseudofunctor` is induced by
`S2667PullFunctor_id`. -/
theorem S2667Fiber_mapId (V : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) :
    (S2667FiberPseudofunctor l F D).mapId V =
      eqToIso (congrArg CategoryTheory.Functor.toCatHom (S2667PullFunctor_id l F D V.as)) := rfl

end LeanFormal.IUT.XiFPaper.S2667FiberCoherenceActual
