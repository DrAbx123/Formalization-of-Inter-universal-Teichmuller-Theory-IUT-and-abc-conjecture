/-
S2811P6: the hom presheaf of the represented etale pseudofunctor is P, and P is an
etale sheaf; hence the represented pseudofunctor is a prestack.

Actual content (no placeholders, no extra axioms):
* presheafHom_obj_eq: objectwise description of the hom presheaf of the represented
  pseudofunctor.
* presheafHomIso: presheafHom M N is isomorphic to P M.as N.as; both sides are objectwise
  subsingletons, so naturality and the iso laws are automatic.
* P_isSheaf: P F X S m n is a sheaf for the over-topology. The only input is
  subcanonicity of the big etale site (S2811_yoneda_isSheaf): separatedness of
  yoneda.obj X along the covering sieve Sieve.overEquiv Y R turns the local
  equalities supplied by a compatible family into the global equality.
* presheafHom_isSheaf, schemeRepresentableEtalePseudofunctor_isPrestack.
-/
import tmp.sheaf.xif.paper.S2811P5Actual
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
set_option linter.unusedVariables false
set_option linter.checkUnivs false

universe u

namespace LeanFormal.IUT.XiFPaper.S2811P6PrestackActual

open LeanFormal.IUT.XiFPaper.S2811P5Actual
open LeanFormal.IUT.XiFPaper.S2811IsPrestackActual

variable (F : Type u) [Field F] (X : Iut.SchemeOverField F)

/-! ### Step 1: objectwise description of the hom presheaf -/

/-- The value of the hom presheaf of the represented pseudofunctor at T is the type of
morphisms between the two pullbacks; it is the subsingleton equality type we expect. -/
lemma presheafHom_obj_eq (S : Iut.SchemeOverField F)
    (M N : (Iut.schemeRepresentableEtalePseudofunctor F X).obj (LocallyDiscrete.mk (op S)))
    (T : (Over S)ᵒᵖ) :
    ((Iut.schemeRepresentableEtalePseudofunctor F X).presheafHom M N).obj T
      = (Discrete.mk (T.unop.hom ≫ M.as) ⟶ Discrete.mk (T.unop.hom ≫ N.as)) := rfl

/-- The hom presheaf of the represented pseudofunctor is objectwise a subsingleton. -/
lemma presheafHom_subsingleton (S : Iut.SchemeOverField F)
    (M N : (Iut.schemeRepresentableEtalePseudofunctor F X).obj (LocallyDiscrete.mk (op S)))
    (T : (Over S)ᵒᵖ) :
    Subsingleton (((Iut.schemeRepresentableEtalePseudofunctor F X).presheafHom M N).obj T) := by
  rw [presheafHom_obj_eq F X S M N T]
  infer_instance

/-- Objectwise map from the hom presheaf to the subterminal presheaf P. -/
def presheafHomToP (S : Iut.SchemeOverField F)
    (M N : (Iut.schemeRepresentableEtalePseudofunctor F X).obj (LocallyDiscrete.mk (op S)))
    (T : (Over S)ᵒᵖ) :
    ((Iut.schemeRepresentableEtalePseudofunctor F X).presheafHom M N).obj T ⟶
      (P F X S M.as N.as).obj T :=
  ↾fun y => ULift.up ⟨(), Discrete.eq_of_hom (presheafHom_obj_eq F X S M N T ▸ y)⟩

/-- Objectwise inverse map from P to the hom presheaf. -/
def presheafHomOfP (S : Iut.SchemeOverField F)
    (M N : (Iut.schemeRepresentableEtalePseudofunctor F X).obj (LocallyDiscrete.mk (op S)))
    (T : (Over S)ᵒᵖ) :
    (P F X S M.as N.as).obj T ⟶
      ((Iut.schemeRepresentableEtalePseudofunctor F X).presheafHom M N).obj T :=
  ↾fun x => (presheafHom_obj_eq F X S M N T).symm ▸ Discrete.eqToHom' x.down.2

/-- The hom presheaf of the representable pseudofunctor is P. -/
noncomputable def presheafHomIso (S : Iut.SchemeOverField F)
    (M N : (Iut.schemeRepresentableEtalePseudofunctor F X).obj (LocallyDiscrete.mk (op S))) :
    (Iut.schemeRepresentableEtalePseudofunctor F X).presheafHom M N ≅ P F X S M.as N.as :=
  NatIso.ofComponents
    (fun T => {
      hom := presheafHomToP F X S M N T
      inv := presheafHomOfP F X S M N T
      hom_inv_id := by
        haveI := presheafHom_subsingleton F X S M N T
        apply ConcreteCategory.hom_ext
        intro x
        simp only [types_comp_apply, types_id_apply]
        exact Subsingleton.elim _ _
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro y
        simp only [types_comp_apply, types_id_apply]
        exact Subsingleton.elim _ _ })
    (by
      intro T₁ T₂ p
      apply ConcreteCategory.hom_ext
      intro y
      simp only [types_comp_apply]
      exact Subsingleton.elim _ _)

/-! ### Step 2: P is a sheaf -/

/-- P F X S m n is a sheaf for the etale topology on Over S. -/
theorem P_isSheaf (S : Iut.SchemeOverField F) (m n : S ⟶ X) :
    Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology F).over S) (P F X S m n) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro Y R hR x _
  have hyon :
      Presieve.IsSheaf (Iut.SchemeOverField.etaleTopology F) (yoneda.obj X) :=
    (isSheaf_iff_isSheaf_of_type (Iut.SchemeOverField.etaleTopology F) (yoneda.obj X)).mp
      (S2811_yoneda_isSheaf F X)
  have hEq : Y.hom ≫ m = Y.hom ≫ n :=
    (Presieve.IsSheaf.isSeparated hyon ((Sieve.overEquiv Y) R) hR).ext
      (fun {Z} {f : Z ⟶ Y.left} hf => by
        have hmem : R.arrows (Over.homMk (U := Over.mk (f ≫ Y.hom)) (V := Y) f rfl) :=
          ((Sieve.overEquiv_iff R) f).mp hf
        have hloc :
            (Over.mk (f ≫ Y.hom)).hom ≫ m = (Over.mk (f ≫ Y.hom)).hom ≫ n :=
          (x (Over.homMk (U := Over.mk (f ≫ Y.hom)) (V := Y) f rfl) hmem).down.2
        show f ≫ (Y.hom ≫ m) = f ≫ (Y.hom ≫ n)
        rw [← Category.assoc, ← Category.assoc]
        exact hloc)
  refine ⟨ULift.up ⟨(), hEq⟩, ?_, ?_⟩
  · intro Z f hf
    exact Subsingleton.elim _ _
  · intro t ht
    exact Subsingleton.elim _ _

/-- The hom presheaf of the represented pseudofunctor is a sheaf. -/
theorem presheafHom_isSheaf (S : Iut.SchemeOverField F)
    (M N : (Iut.schemeRepresentableEtalePseudofunctor F X).obj (LocallyDiscrete.mk (op S))) :
    Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology F).over S)
      ((Iut.schemeRepresentableEtalePseudofunctor F X).presheafHom M N) :=
  (Presheaf.isSheaf_of_iso_iff (presheafHomIso F X S M N)).mpr (P_isSheaf F X S M.as N.as)

/-- The represented etale pseudofunctor is a prestack. -/
instance schemeRepresentableEtalePseudofunctor_isPrestack :
    (Iut.schemeRepresentableEtalePseudofunctor F X).IsPrestack
      (Iut.SchemeOverField.etaleTopology F) :=
  ⟨fun {S} M N => presheafHom_isSheaf F X S M N⟩

#check P_isSheaf
#check presheafHomIso
#check presheafHom_isSheaf
#check schemeRepresentableEtalePseudofunctor_isPrestack
#print axioms presheafHomIso
#print axioms P_isSheaf
#print axioms presheafHom_isSheaf
#print axioms schemeRepresentableEtalePseudofunctor_isPrestack

end LeanFormal.IUT.XiFPaper.S2811P6PrestackActual
end
