import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace Probe4

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual

universe u

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}

/-- The relation identifying two cover maps whose underlying strong
transformations are 2-isomorphic. -/
def CoverMapRel {A B : OrbicurveFiniteEtaleCover X}
    (f g : OrbicurveFiniteEtaleCoverMap A B) : Prop :=
  Nonempty (f.map ≅ g.map)

lemma coverMapRel_refl {A B : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B) : CoverMapRel f f :=
  ⟨Iso.refl f.map⟩

lemma coverMapRel_symm {A B : OrbicurveFiniteEtaleCover X}
    {f g : OrbicurveFiniteEtaleCoverMap A B}
    (h : CoverMapRel f g) : CoverMapRel g f := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

lemma coverMapRel_trans {A B : OrbicurveFiniteEtaleCover X}
    {f g h : OrbicurveFiniteEtaleCoverMap A B}
    (hfg : CoverMapRel f g) (hgh : CoverMapRel g h) : CoverMapRel f h := by
  rcases hfg with ⟨e₁⟩
  rcases hgh with ⟨e₂⟩
  exact ⟨e₁.trans e₂⟩

/-- The Type (u+1) quotient of cover maps by 2-isomorphism of underlying
strong transformations.  For F : Type 0 this is Type 1. -/
abbrev CoverMapClass (A B : OrbicurveFiniteEtaleCover X) : Type (u + 1) :=
  Quot (fun f g : OrbicurveFiniteEtaleCoverMap A B => CoverMapRel f g)

/-- If the second argument is replaced by a 2-isomorphic map, the composite
underlying map is 2-isomorphic. -/
lemma coverMapRel_comp_right {A B C : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    {g g' : OrbicurveFiniteEtaleCoverMap B C}
    (hg : CoverMapRel g g') :
    CoverMapRel (S1641CoverMapComp f g) (S1641CoverMapComp f g') := by
  rcases hg with ⟨eg⟩
  exact ⟨Bicategory.whiskerLeftIso f.map eg⟩

/-- If the first argument is replaced by a 2-isomorphic map, the composite
underlying map is 2-isomorphic. -/
lemma coverMapRel_comp_left {A B C : OrbicurveFiniteEtaleCover X}
    {f f' : OrbicurveFiniteEtaleCoverMap A B}
    (g : OrbicurveFiniteEtaleCoverMap B C)
    (hf : CoverMapRel f f') :
    CoverMapRel (S1641CoverMapComp f g) (S1641CoverMapComp f' g) := by
  rcases hf with ⟨ef⟩
  exact ⟨Bicategory.whiskerRightIso ef g.map⟩

noncomputable def CoverMapClassComp {A B C : OrbicurveFiniteEtaleCover X}
    (f : CoverMapClass (A := A) (B := B)) (g : CoverMapClass (B := B) (C := C)) :
    CoverMapClass (A := A) (C := C) :=
  Quot.map₂ (fun f g => S1641CoverMapComp f g)
    (fun _ _ _ hg => coverMapRel_comp_right _ hg)
    (fun _ _ _ hf => coverMapRel_comp_left _ hf) f g

noncomputable def CoverMapClassId (A : OrbicurveFiniteEtaleCover X) :
    CoverMapClass (A := A) (B := A) :=
  Quot.mk _ (S1641CoverMapId A)

noncomputable def CoverCategoryStruct11 :
    CategoryStruct (OrbicurveFiniteEtaleCover X) where
  Hom := CoverMapClass
  id := CoverMapClassId
  comp := CoverMapClassComp

end Probe4
