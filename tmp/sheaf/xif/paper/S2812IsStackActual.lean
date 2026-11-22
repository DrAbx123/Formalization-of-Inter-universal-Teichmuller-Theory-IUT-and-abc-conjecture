/-
S2812: the scheme-representable etale pseudofunctor is an etale stack.

Actual content (no placeholders, no extra axioms):
* map_obj_eq: pulling back an object of the fiber over S along p : Y -> S is
  precomposition, definitionally.
* descentFamily, descentFamily_compatible: a descent datum for a cover gives a compatible
  family of elements of yoneda.obj X.
* gluedSection and gluedSection_fac: subcanonicity of the etale topology
  (S2811_yoneda_isSheaf) glues that compatible family to a section of yoneda.obj X.
* descentDataIso, essSurj_toDescentData: every descent datum is isomorphic to one in the
  image of toDescentData.
* isStackFor_sieve, schemeRepresentableEtalePseudofunctor_isStack.
-/
import tmp.sheaf.xif.paper.S2811P6PrestackActual

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
set_option linter.unusedVariables false
set_option linter.checkUnivs false

universe u

namespace LeanFormal.IUT.XiFPaper.S2812IsStackActual

open LeanFormal.IUT.XiFPaper.S2811IsPrestackActual
open LeanFormal.IUT.XiFPaper.S2811P5Actual
open LeanFormal.IUT.XiFPaper.S2811P6PrestackActual

variable (F : Type u) [Field F] (X : Iut.SchemeOverField F)

/-! ### Step 0: the pseudofunctor under consideration -/

/-- The category-valued etale pseudofunctor represented by the scheme X. -/
abbrev fiber : Iut.EtaleStackPseudofunctor F :=
  Iut.schemeRepresentableEtalePseudofunctor F X

/-! ### Step 1: pullbacks of objects of the fiber -/

/-- Pulling back an object of the fiber over S along p : Y -> S is precomposition
with p; this holds definitionally. -/
lemma map_obj_eq {S : Iut.SchemeOverField F} (M : (fiber F X).obj (LocallyDiscrete.mk (op S)))
    {Y : Iut.SchemeOverField F} (p : Y ⟶ S) :
    ((fiber F X).map p.op.toLoc).toFunctor.obj M = Discrete.mk (p ≫ M.as) := rfl

/-- The morphism types in the fiber of the represented pseudofunctor are subsingletons. -/
instance subsingleton_hom_fiber {Y : Iut.SchemeOverField F}
    (A B : (fiber F X).obj (LocallyDiscrete.mk (op Y))) : Subsingleton (A ⟶ B) :=
  inferInstanceAs (Subsingleton (Discrete.mk A.as ⟶ Discrete.mk B.as))

/-- A morphism of a descent datum gives an equality of the corresponding restrictions. -/
lemma hom_as_eq {S : Iut.SchemeOverField F} {ι : Type u}
    {Xf : ι → Iut.SchemeOverField F} {fam : ∀ i, Xf i ⟶ S}
    (D : (fiber F X).DescentData fam)
    {Y : Iut.SchemeOverField F} (q : Y ⟶ S) {i₁ i₂ : ι}
    (f₁ : Y ⟶ Xf i₁) (f₂ : Y ⟶ Xf i₂)
    (hf₁ : f₁ ≫ fam i₁ = q) (hf₂ : f₂ ≫ fam i₂ = q) :
    f₁ ≫ (D.obj i₁).as = f₂ ≫ (D.obj i₂).as := by
  have h := Discrete.eq_of_hom (D.hom q f₁ f₂ hf₁ hf₂)
  simpa only [map_obj_eq] using h

/-! ### Step 2: the compatible family of a descent datum -/

/-- The action of yoneda.obj X on an opposite morphism is precomposition. -/
lemma yoneda_map_apply {Y Z : Iut.SchemeOverField F} (g : Z ⟶ Y) (y : Y ⟶ X) :
    (yoneda.obj X).map g.op y = g ≫ y := rfl

/-- The family of elements of yoneda.obj X attached to a descent datum: the datum
consists of morphisms U -> X for each arrow U -> S of the sieve. -/
def descentFamily (S : Iut.SchemeOverField F) (R : Sieve S)
    (D : (fiber F X).DescentData (fun (f : R.arrows.category) => f.obj.hom)) :
    Presieve.FamilyOfElements (yoneda.obj X) R.arrows :=
  fun {Y} f hf => (D.obj ⟨Over.mk f, hf⟩).as

/-- The family attached to a descent datum is compatible. -/
lemma descentFamily_compatible (S : Iut.SchemeOverField F) (R : Sieve S)
    (D : (fiber F X).DescentData (fun (f : R.arrows.category) => f.obj.hom)) :
    (descentFamily F X S R D).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
  change g₁ ≫ descentFamily F X S R D f₁ h₁ = g₂ ≫ descentFamily F X S R D f₂ h₂
  have h := Discrete.eq_of_hom
    (D.hom (Y := Z) (q := g₁ ≫ f₁)
      (i₁ := (⟨Over.mk f₁, h₁⟩ : R.arrows.category))
      (i₂ := (⟨Over.mk f₂, h₂⟩ : R.arrows.category)) g₁ g₂ rfl comm.symm)
  simp only [map_obj_eq] at h
  change g₁ ≫ (D.obj ⟨Over.mk f₁, h₁⟩).as = g₂ ≫ (D.obj ⟨Over.mk f₂, h₂⟩).as
  exact h

/-! ### Step 3: gluing via the sheaf property of yoneda.obj X -/

/-- yoneda.obj X satisfies the sheaf condition for the arrows of a covering sieve. -/
lemma yoneda_isSheafFor (S : Iut.SchemeOverField F) (R : Sieve S)
    (hR : R ∈ Iut.SchemeOverField.etaleTopology F S) :
    Presieve.IsSheafFor (yoneda.obj X) R.arrows :=
  ((isSheaf_iff_isSheaf_of_type (Iut.SchemeOverField.etaleTopology F) (yoneda.obj X)).mp
    (S2811_yoneda_isSheaf F X)) R hR

/-- The section of yoneda.obj X on S obtained by gluing the descent datum. -/
noncomputable def gluedSection (S : Iut.SchemeOverField F) (R : Sieve S)
    (hR : R ∈ Iut.SchemeOverField.etaleTopology F S)
    (D : (fiber F X).DescentData (fun (f : R.arrows.category) => f.obj.hom)) : S ⟶ X :=
  (yoneda_isSheafFor F X S R hR (descentFamily F X S R D)
    (descentFamily_compatible F X S R D)).choose

/-- The glued section is an amalgamation of the family. -/
lemma gluedSection_isAmalgamation (S : Iut.SchemeOverField F) (R : Sieve S)
    (hR : R ∈ Iut.SchemeOverField.etaleTopology F S)
    (D : (fiber F X).DescentData (fun (f : R.arrows.category) => f.obj.hom)) :
    (descentFamily F X S R D).IsAmalgamation (gluedSection F X S R hR D) :=
  (yoneda_isSheafFor F X S R hR (descentFamily F X S R D)
    (descentFamily_compatible F X S R D)).choose_spec.1

/-- The face condition of the glued section. -/
lemma gluedSection_fac (S : Iut.SchemeOverField F) (R : Sieve S)
    (hR : R ∈ Iut.SchemeOverField.etaleTopology F S)
    (D : (fiber F X).DescentData (fun (f : R.arrows.category) => f.obj.hom))
    {Y : Iut.SchemeOverField F} (f : Y ⟶ S) (hf : R.arrows f) :
    f ≫ gluedSection F X S R hR D = (D.obj ⟨Over.mk f, hf⟩).as :=
  gluedSection_isAmalgamation F X S R hR D f hf

/-! ### Step 4: effectiveness of descent -/

/-- The object of the descent datum over the index i, computed on underlying morphisms. -/
lemma toDescentData_obj_as {S : Iut.SchemeOverField F} (R : Sieve S)
    (t : S ⟶ X) (i : R.arrows.category) :
    (((((fiber F X).toDescentData (fun (f : R.arrows.category) => f.obj.hom)).obj
      (Discrete.mk t))).obj i).as = i.obj.hom ≫ t := rfl

/-- A descent datum is isomorphic to the descent datum of its glued section. -/
noncomputable def descentDataIso (S : Iut.SchemeOverField F) (R : Sieve S)
    (hR : R ∈ Iut.SchemeOverField.etaleTopology F S)
    (D : (fiber F X).DescentData (fun (f : R.arrows.category) => f.obj.hom)) :
    ((fiber F X).toDescentData (fun (f : R.arrows.category) => f.obj.hom)).obj
      (Discrete.mk (gluedSection F X S R hR D)) ≅ D :=
  Pseudofunctor.DescentData.isoMk
    (fun i => Discrete.eqToIso (by
      rw [toDescentData_obj_as]
      exact gluedSection_fac F X S R hR D i.obj.hom i.property))
    (fun _ _ _ _ _ _ _ _ => Subsingleton.elim _ _)

/-- The functor toDescentData associated with a covering sieve is essentially surjective. -/
lemma essSurj_toDescentData (S : Iut.SchemeOverField F) (R : Sieve S)
    (hR : R ∈ Iut.SchemeOverField.etaleTopology F S) :
    ((fiber F X).toDescentData (fun (f : R.arrows.category) => f.obj.hom)).EssSurj :=
  ⟨fun D => ⟨Discrete.mk (gluedSection F X S R hR D), ⟨descentDataIso F X S R hR D⟩⟩⟩

/-! ### Step 5: the stack condition -/

/-- Effective descent for the arrows of a covering sieve. -/
lemma isStackFor_sieve (S : Iut.SchemeOverField F) (R : Sieve S)
    (hR : R ∈ Iut.SchemeOverField.etaleTopology F S) :
    (fiber F X).IsStackFor R.arrows := by
  haveI hpre : (fiber F X).IsPrestack (Iut.SchemeOverField.etaleTopology F) :=
    schemeRepresentableEtalePseudofunctor_isPrestack F X
  have hff :
      ((fiber F X).toDescentData (fun (f : R.arrows.category) => f.obj.hom)).FullyFaithful :=
    ((fiber F X).isPrestackFor' R hR).fullyFaithful
  exact ⟨⟨hff.faithful, hff.full, essSurj_toDescentData F X S R hR⟩⟩

/-- **Main result**: the pseudofunctor represented by a scheme over a field is an etale
stack. -/
instance schemeRepresentableEtalePseudofunctor_isStack :
    (Iut.schemeRepresentableEtalePseudofunctor F X).IsStack
      (Iut.SchemeOverField.etaleTopology F) :=
  Pseudofunctor.IsStack.of_isStackFor (fun S R hR => isStackFor_sieve F X S R hR)

#check schemeRepresentableEtalePseudofunctor_isStack
#print axioms schemeRepresentableEtalePseudofunctor_isStack
#print axioms essSurj_toDescentData
#print axioms isStackFor_sieve

end LeanFormal.IUT.XiFPaper.S2812IsStackActual
end