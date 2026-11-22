import tmp.sheaf.xif.paper.S2619ActionGroupoidFiberSkeleton

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.S2668FiberCoherenceActual

universe u
variable {l : PrimeGeFive} {F : Type u} [CommRing F]
variable (D : S2619ActionGroupoidData (l := l) (F := F))

/-- Pullback along the identity is the identity functor on the fiber. -/
theorem S2668PullFunctor_id (V : (Iut.SchemeOverField F)ᵒᵖ) :
    S2619PullFunctor (l := l) (F := F) (D := D) (𝟙 V) =
      CategoryTheory.Functor.id (↑(S2619FiberAt (l := l) (F := F) D V)) := by
  refine CategoryTheory.Functor.hext (fun X => rfl) (fun X Y eta => ?_)
  rcases X with ⟨xst, xback⟩
  rcases Y with ⟨yst, yback⟩
  cases xst
  cases yst
  rfl

/-- Pullback along a composite is the composite of the pullbacks. -/
theorem S2668PullFunctor_comp {U V W : (Iut.SchemeOverField F)ᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    S2619PullFunctor (l := l) (F := F) (D := D) (f ≫ g) =
      S2619PullFunctor (l := l) (F := F) (D := D) f ⋙
        S2619PullFunctor (l := l) (F := F) (D := D) g := by
  refine CategoryTheory.Functor.hext (fun X => rfl) (fun X Y eta => ?_)
  rcases X with ⟨xst, xback⟩
  rcases Y with ⟨yst, yback⟩
  cases xst
  cases yst
  rcases eta with ⟨k, hk⟩
  rfl

/-- The strict functor `V ↦ S2619FiberAt V` on the opposite category, whose arrow maps
are the pullback functors. -/
noncomputable def S2668FiberFunctor : (Iut.SchemeOverField F)ᵒᵖ ⥤ Cat.{0, u} where
  obj V := S2619FiberAt (l := l) (F := F) D V
  map {_ _} h := (S2619PullFunctor (l := l) (F := F) (D := D) h).toCatHom
  map_id V := by
    apply CategoryTheory.Cat.ext
    exact S2668PullFunctor_id (l := l) (F := F) D V
  map_comp {_ _ _} f g := by
    apply CategoryTheory.Cat.ext
    exact S2668PullFunctor_comp (l := l) (F := F) D f g

/-- The pseudofunctor of fibers: an object `V` is sent to the action-groupoid fiber
`S2619FiberAt D V`, and an arrow `f` to the pullback functor `S2619PullFunctor f`. -/
noncomputable def S2668FiberPseudofunctor :
    LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{0, u} :=
  Functor.toPseudofunctor' (S2668FiberFunctor (l := l) (F := F) D)

lemma S2668FiberPseudofunctor_obj (V : (Iut.SchemeOverField F)ᵒᵖ) :
    (S2668FiberPseudofunctor (l := l) (F := F) D).obj (LocallyDiscrete.mk V) =
      S2619FiberAt (l := l) (F := F) D V := rfl

lemma S2668FiberPseudofunctor_map {V V' : (Iut.SchemeOverField F)ᵒᵖ} (f : V ⟶ V') :
    (S2668FiberPseudofunctor (l := l) (F := F) D).map
        f.toLoc =
      (S2619PullFunctor (l := l) (F := F) (D := D) f).toCatHom := rfl

#print axioms S2668PullFunctor_id
#print axioms S2668PullFunctor_comp
#print axioms S2668FiberPseudofunctor

end LeanFormal.IUT.XiFPaper.S2668FiberCoherenceActual
end

