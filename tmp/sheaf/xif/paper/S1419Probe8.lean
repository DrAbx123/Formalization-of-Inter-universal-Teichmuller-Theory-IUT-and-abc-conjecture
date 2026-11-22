import tmp.sheaf.n8.closure.DiscreteSheafIsStack
import Mathlib.CategoryTheory.Sites.Sheaf

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack

namespace S1419Probe8

universe v u

variable {C : Type u} [Category.{v} C]

noncomputable def fam (P : Cᵒᵖ ⥤ Type v) {X : C} (S : Sieve X)
    (D : (discretePseudo P).DescentData (fun i : S.arrows.category => i.obj.hom)) :
    Presieve.FamilyOfElements P S.arrows :=
  fun _ f hf => (D.obj ⟨Over.mk f, hf⟩).as

variable (P : Cᵒᵖ ⥤ Type v) {X : C} (S : Sieve X)

theorem fam_compatible (D : (discretePseudo P).DescentData
    (fun i : S.arrows.category => i.obj.hom)) :
    (fam P S D).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro Y Z u g hu
  let i₁ : S.arrows.category := ⟨Over.mk u, hu⟩
  let i₂ : S.arrows.category := ⟨Over.mk (g ≫ u), S.downward_closed hu g⟩
  have hD := D.hom (Y := Z) (q := g ≫ u) (i₁ := i₁) (i₂ := i₂)
    (f₁ := g) (f₂ := 𝟙 Z) (by rfl) (by exact Category.id_comp (g ≫ u))
  have hEq := Discrete.eq_of_hom hD
  change (Discrete.mk (P.map g.op (D.obj i₁).as)).as =
    (Discrete.mk (P.map (𝟙 Z).op (D.obj i₂).as)).as at hEq
  simp only [Discrete.mk_as] at hEq
  rw [show P.map (𝟙 Z).op (D.obj i₂).as = (D.obj i₂).as by simp] at hEq
  exact hEq.symm

variable (D : (discretePseudo P).DescentData (fun i : S.arrows.category => i.obj.hom))
  (hS : Presieve.IsSheafFor P S.arrows)

noncomputable def glue : P.obj (Opposite.op X) :=
  hS.amalgamate (fam P S D) (fam_compatible P S D)

theorem glue_spec (i : S.arrows.category) :
    P.map i.obj.hom.op (glue P S D hS) = (D.obj i).as := by
  have h := hS.isAmalgamation (fam_compatible P S D) i.obj.hom i.property
  exact h

theorem toDescentData_glue_obj (i : S.arrows.category) :
    (((discretePseudo P).toDescentData (fun i : S.arrows.category => i.obj.hom)).obj
        (Discrete.mk (glue P S D hS))).obj i = D.obj i := by
  change Discrete.mk (P.map i.obj.hom.op (glue P S D hS)) = D.obj i
  rw [glue_spec P S D hS i, Discrete.mk_as]

noncomputable def essSurj : ((discretePseudo P).toDescentData
    (fun i : S.arrows.category => i.obj.hom)).EssSurj where
  mem_essImage D := ⟨Discrete.mk (glue P S D hS), ⟨by
    refine Pseudofunctor.DescentData.isoMk (fun i => eqToIso (toDescentData_glue_obj P S D hS i)) ?_
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    exact @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _⟩⟩

end S1419Probe8

end
