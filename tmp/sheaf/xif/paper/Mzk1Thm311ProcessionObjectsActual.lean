import tmp.sheaf.lana_latest.Iut.Multiradial.Spec

/-! Mainline (A517-5): Theorem 3.11 procession objects (the input groupoid of the
multiradial algorithm), referenced from the real LANA-latest `Multiradial/Spec.lean`:
`Procession C n` (an `n`-procession of capsules `P_j ↪ P_{j+1}` as the collection of all
capsule-full poly-morphisms), its groupoid `Hom` with `ext'`, `id`, `comp`, `inv`, the label
indeterminacy `labelPerm` and the surjectivity of relabelling `exists_aut_labelPerm`, and the
change-of-components functor `map` (mono-analyticization `D ↦ D^⊢`). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm311ProcessionObjectsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

section Objects

variable (C : Type*) [Category C] (n : ℕ)

/-- **O2 object**: an `n`-procession of objects of `C` (IUT I, Definition 4.10; the input of
  the multiradial algorithm, `Prc(n,∘D^⊢_T)`). -/
abbrev Thm311Procession := Iut.Multiradial.Procession C n

/-- An isomorphism of processions (capsule-wise bijections of index sets and component
  isomorphisms). -/
abbrev thm311ProcessionHom (P Q : Thm311Procession C n) := P ⟶ Q

/-- The identity isomorphism of a procession. -/
def thm311ProcessionHomId (P : Thm311Procession C n) : P ⟶ P :=
  𝟙 P

/-- Composition of procession isomorphisms. -/
def thm311ProcessionHomComp {P Q S : Thm311Procession C n} (f : P ⟶ Q) (g : Q ⟶ S) :
    P ⟶ S :=
  f ≫ g

/-- Inverse of a procession isomorphism. -/
def thm311ProcessionHomInv {P Q : Thm311Procession C n} (f : P ⟶ Q) : Q ⟶ P :=
  Iut.Multiradial.Procession.Hom.inv f

/-- Two procession isomorphisms with the same bijections and component maps are equal
  (LANA real theorem). -/
theorem thm311ProcessionHom_ext' {P Q : Thm311Procession C n} {f g : P ⟶ Q}
    (hp : Iut.Multiradial.Procession.Hom.perm f =
      Iut.Multiradial.Procession.Hom.perm g)
    (hi : ∀ j t, (Iut.Multiradial.Procession.Hom.iso f j t).hom ≫
        eqToHom (by rw [hp]) = (Iut.Multiradial.Procession.Hom.iso g j t).hom) :
    f = g :=
  Iut.Multiradial.Procession.Hom.ext' hp hi

/-- The label bijections of an automorphism of a procession: the (Ind1) label indeterminacy
  (IANA real def, IUT III Remark 3.11.2(ii)). -/
def thm311ProcessionLabelPerm {P : Thm311Procession C n} (σ : Aut P) (j : Fin n) :
    Equiv.Perm (Fin (j + 1)) :=
  Iut.Multiradial.Procession.labelPerm σ j

/-- **Every relabelling is realized by an automorphism** when capsule components are
  isomorphic: the label part of (Ind1) is the full product of symmetric groups (LANA real
  theorem). -/
theorem thm311Procession_exists_aut_labelPerm {P : Thm311Procession C n}
    (hiso : ∀ j t t', Nonempty (P.obj j t ≅ P.obj j t'))
    (π : (j : Fin n) → Equiv.Perm (Fin (j + 1))) :
    ∃ σ : Aut P, ∀ j, thm311ProcessionLabelPerm σ j = π j :=
  Iut.Multiradial.Procession.exists_aut_labelPerm hiso π

/-- **Change of components** (mono-analyticization `D ↦ D^⊢`): a functor `C ⥤ D` induces a
  functor of processions (LANA real def). -/
def thm311ProcessionMap {Dcat : Type u} [Category.{v} Dcat] (F : C ⥤ Dcat) :
    Thm311Procession C n ⥤ Thm311Procession Dcat n :=
  Iut.Multiradial.Procession.map F

end Objects

end

end LeanFormal.IUT.XiFPaper.Mzk1Thm311ProcessionObjectsActual