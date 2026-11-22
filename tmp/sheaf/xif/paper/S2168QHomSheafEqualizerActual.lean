import tmp.sheaf.xif.paper.S2160QHomSheafActual
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Sites.SheafOfTypes

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2160QHomSheafActual
open LeanFormal.IUT.XiFPaper.S2158QStackActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2168QHomSheafEqualizerActual

universe v

/-- The equalizer sheaf lemma required for the Q hom-presheaf: the pointwise
equalizer of two morphisms of sheaves of types is a sheaf. -/
def S2168EqualizerSheafLemma (C : Type 1) [Category.{v} C]
    (J : GrothendieckTopology C) : Prop :=
  forall (P R : Cᵒᵖ ⥤ Type)
    (hP : Presheaf.IsSheaf J P) (hR : Presheaf.IsSheaf J R)
    (f g : P ⟶ R),
    Presheaf.IsSheaf J (Limits.equalizer f g)

/-- The equalizer form of a Q hom-presheaf at fixed S,M,N. -/
structure S2168QHomEqualizerData
    (S : Iut.SchemeOverField S1726K)
    (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S))) where
  P : ((Over S)ᵒᵖ ⥤ Type)
  R : ((Over S)ᵒᵖ ⥤ Type)
  hP : Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S) P
  hR : Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S) R
  f : P ⟶ R
  g : P ⟶ R
  iso : S2152Q.presheafHom M N ≅ Limits.equalizer f g

/-- The exact identification needed: every Q hom-presheaf is an equalizer of
two morphisms between sheaves of types on the slice site. -/
def S2168QHomEqualizerIdentification : Prop :=
  forall (S : Iut.SchemeOverField S1726K)
    (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S))),
    Nonempty (S2168QHomEqualizerData  S M N)

/-- Conditional actual: the equalizer sheaf lemma plus the equalizer
identification imply the Q hom-presheaf sheaf condition. -/
theorem S2160QHomSheafFor_of_equalizer
    (hLemma : forall (S : Iut.SchemeOverField S1726K),
      S2168EqualizerSheafLemma (C := Over S) ((Iut.SchemeOverField.etaleTopology S1726K).over S))
    (hId : S2168QHomEqualizerIdentification ) :
    S2160QHomSheafFor := by
  intro S M N
  obtain ⟨D⟩ := hId S M N
  have hE : Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S)
      (Limits.equalizer D.f D.g) :=
    hLemma S D.P D.R D.hP D.hR D.f D.g
  exact (Presheaf.isSheaf_of_iso_iff D.iso).mpr hE

/-- The exact first missing in equalizer form. -/
def S2168QHomEqualizerFirstMissing : Prop :=
  S2168QHomEqualizerIdentification 

#print axioms S2160QHomSheafFor_of_equalizer

end LeanFormal.IUT.XiFPaper.S2168QHomSheafEqualizerActual

end
