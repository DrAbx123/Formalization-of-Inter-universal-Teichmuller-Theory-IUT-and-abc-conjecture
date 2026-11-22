import tmp.sheaf.xif.paper.S2433D9FinalActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2433D9FinalActual
open LeanFormal.IUT.XiFPaper.S2430D9CloseActual
open LeanFormal.IUT.XiFPaper.S2103D9PrestackActual
open LeanFormal.IUT.XiFPaper.S2134D9DescentActual
open LeanFormal.IUT.XiFPaper.S2428D9FinalActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S2332PsubCorrectActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2434D9AttackActual

universe v u v' u'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A]

/-- The exact pullHom form of the slice-push naturality missing, re-exported
from S2103 as an actual equivalence. -/
theorem S2434SlicePush_iff_pullHom {S : C} (M N : Sheaf (J.over S) A) :
    SlicePushNaturality (J := J) (A := A) M N ↔
      ∀ ⦃X₁ X₂ : (Over S)ᵒᵖ⦄ (f : X₁ ⟶ X₂)
        (φ : (CategoryTheory.sheafHom' (J := J.over S) M N).obj X₁),
        (slicePush (J := J) (A := A) X₂.unop).map
            (((J.over S).overMapPullback A f.unop).map φ) =
          Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := J.pseudofunctorOver A)
            ((slicePush (J := J) (A := A) X₁.unop).map φ) f.unop.left X₂.unop.hom X₂.unop.hom :=
  slicePushNaturality_iff_pullHom (J := J) (A := A) M N

variable (S : Iut.SchemeOverField S1726K)

/-- The exact sign projection input. -/
abbrev S2434SignProjectionMissing : Prop := S2428PsubNatIsoMissing S

/-- The exact general effective-descent input. -/
abbrev S2434EffDescentMissing : Prop := S2134EffDescentOnEtaleFamilies S1726K

/-- The exact slice-push naturality input (D9 prestack half). -/
abbrev S2434PrestackMissing : Prop := S2103FirstMissing S1726K

/-- Conditional Psub NatIso, re-exported. -/
noncomputable def S2434PsubNatIso_of_missing
    (h : S2434SignProjectionMissing S)
    (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S))) :
    S2152Q.presheafHom M N ≅ S2332Psub S M N :=
  S2433PsubNatIso_of_missing S h M N

/-- The exact three-input D9 decomposition, re-exported. -/
theorem S2434D9Missing_iff_three :
    S2428D9Missing S ↔
      S2103FirstMissing S1726K ∧
        S2134EffDescentOnEtaleFamilies S1726K ∧
          S2434SignProjectionMissing S :=
  S2433D9Missing_iff_three S

#print axioms S2434SlicePush_iff_pullHom
#print axioms S2434D9Missing_iff_three

end LeanFormal.IUT.XiFPaper.S2434D9AttackActual

end
