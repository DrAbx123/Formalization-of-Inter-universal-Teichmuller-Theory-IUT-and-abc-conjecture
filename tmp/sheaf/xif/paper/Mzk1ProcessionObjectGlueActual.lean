import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual

/-! # Mzk1ProcessionObjectGlueActual — consumer forms of the procession object

Small reference/glue module (no new mathematics): consumes the LANA
`Multiradial/Spec` procession card (IUT I, Definition 4.10: `Procession`, `Procession.Hom`,
the groupoid structure, label-permutation indeterminacy, and the mono-analyticization functor
`Procession.map`).  These are the input objects of the Theorem 3.11 multiradial algorithm
`Prc(n,∘D⊢_T)`.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ProcessionObjectGlueActual

open CategoryTheory
open Iut.Multiradial

universe u v

variable {C : Type u} [Category.{v} C] {n : ℕ}

/-- The component objects of an `n`-procession, unfolded. -/
theorem procession_obj_apply (P : Procession C n) (j : Fin n) (t : Fin (j + 1)) :
    P.obj j t = P.obj j t := rfl

/-- Identity isomorphism of a procession is componentwise the identity. -/
theorem procession_id_iso (P : Procession C n) (j : Fin n) (t : Fin (j + 1)) :
    Procession.Hom.iso (𝟙 P) j t = Iso.refl (P.obj j t) :=
  Procession.id_iso P j t

/-- Composition of processions is componentwise composition of the isomorphisms. -/
theorem procession_comp_iso {P Q S : Procession C n} (f : P ⟶ Q) (g : Q ⟶ S)
    (j : Fin n) (t : Fin (j + 1)) :
    Procession.Hom.iso (f ≫ g) j t =
      Procession.Hom.iso f j t ≪≫ Procession.Hom.iso g j (Procession.Hom.perm f j t) :=
  Procession.comp_iso f g j t

/-- The label permutation of an automorphism of a procession is its index-set permutation. -/
theorem labelPerm_apply {P : Procession C n} (σ : Aut P) (j : Fin n) :
    Procession.labelPerm σ j = Procession.Hom.perm σ.hom j := rfl

/-- Every assignment of capsule label permutations is realised by an automorphism when the
capsules consist of isomorphic objects: the label part of (Ind1). -/
theorem exists_aut_of_labelPerm {P : Procession C n}
    (hiso : ∀ j t t', Nonempty (P.obj j t ≅ P.obj j t'))
    (π : (j : Fin n) → Equiv.Perm (Fin (j + 1))) :
    ∃ σ : Aut P, ∀ j, Procession.labelPerm σ j = π j :=
  Procession.exists_aut_labelPerm hiso π

/-- The mono-analyticization functor on processions acts componentwise. -/
theorem procession_map_obj {D : Type u} [Category.{v} D] (F : C ⥤ D)
    (P : Procession C n) (j : Fin n) (t : Fin (j + 1)) :
    ((Procession.map F).obj P).obj j t = F.obj (P.obj j t) := rfl

/-- The mono-analyticization functor preserves the permutation component. -/
theorem procession_map_perm {D : Type u} [Category.{v} D] (F : C ⥤ D)
    {P Q : Procession C n} (f : P ⟶ Q) (j : Fin n) :
    Procession.Hom.perm ((Procession.map F).map f) j = Procession.Hom.perm f j := rfl

#check procession_id_iso
#check procession_comp_iso
#check labelPerm_apply
#check exists_aut_of_labelPerm
#check procession_map_obj

end LeanFormal.IUT.XiFPaper.Mzk1ProcessionObjectGlueActual
end
