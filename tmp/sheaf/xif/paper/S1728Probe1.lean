import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace Probe2

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

lemma coverMapRel_refl {A B} (f : OrbicurveFiniteEtaleCoverMap A B) :
    CoverMapRel f f :=
  ⟨Iso.refl f.map⟩

lemma coverMapRel_symm {A B} {f g : OrbicurveFiniteEtaleCoverMap A B}
    (h : CoverMapRel f g) : CoverMapRel g f := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

lemma coverMapRel_trans {A B} {f g h : OrbicurveFiniteEtaleCoverMap A B}
    (hfg : CoverMapRel f g) (hgh : CoverMapRel g h) : CoverMapRel f h := by
  rcases hfg with ⟨e₁⟩
  rcases hgh with ⟨e₂⟩
  exact ⟨e₁.trans e₂⟩

instance coverMapSetoid (A B : OrbicurveFiniteEtaleCover X) :
    Setoid (OrbicurveFiniteEtaleCoverMap A B) where
  r := CoverMapRel
  iseqv := ⟨coverMapRel_refl, coverMapRel_symm, coverMapRel_trans⟩

/-- The Type 1 quotient of cover maps by 2-isomorphism of underlying
strong transformations. -/
abbrev CoverMapClass (A B : OrbicurveFiniteEtaleCover X) : Type 1 :=
  Quot (coverMapSetoid A B)

example (A B : OrbicurveFiniteEtaleCover X) : Type 1 := CoverMapClass A B

/-- Well-definedness of composition on 2-isomorphism classes. -/
lemma coverMapRel_comp {A B C : OrbicurveFiniteEtaleCover X}
    {f f' : OrbicurveFiniteEtaleCoverMap A B}
    {g g' : OrbicurveFiniteEtaleCoverMap B C}
    (hf : CoverMapRel f f') (hg : CoverMapRel g g') :
    CoverMapRel (S1641CoverMapComp f g) (S1641CoverMapComp f' g') := by
  rcases hf with ⟨ef⟩
  rcases hg with ⟨eg⟩
  refine ⟨?trans⟩
  exact (Bicategory.whiskerRightIso ef g.map).trans
    (Bicategory.whiskerLeftIso f'.map eg)

noncomputable def CoverMapClassComp {A B C : OrbicurveFiniteEtaleCover X}
    (f : CoverMapClass A B) (g : CoverMapClass B C) : CoverMapClass A C :=
  Quot.map₂ (fun f g => S1641CoverMapComp f g)
    (fun _ _ _ _ hf hg => coverMapRel_comp hf hg) f g

noncomputable def CoverMapClassId (A : OrbicurveFiniteEtaleCover X) : CoverMapClass A A :=
  Quot.mk _ (S1641CoverMapId A)

noncomputable def CoverCategoryStruct11 :
    CategoryStruct (OrbicurveFiniteEtaleCover X) where
  Hom := CoverMapClass
  id := CoverMapClassId
  comp := CoverMapClassComp

end Probe2
