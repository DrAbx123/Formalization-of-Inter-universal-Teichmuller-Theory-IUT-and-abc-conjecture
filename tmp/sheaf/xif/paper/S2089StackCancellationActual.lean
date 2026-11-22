import tmp.sheaf.xif.paper.S2088GMapCancellationActual

/-! # S2089: stack cancellation decomposed into presentation data

Right cancellation for representable finite etaleness reduces to building,
from a presentation of `g` at `ptY ≫ g` and a presentation of `f ≫ g`, a
presentation of `f` at `ptY`, plus the scheme-level finite-etale property.
No such presentation is constructed here.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2089StackCancellationActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2088GMapCancellationActual

universe u

/-- Exact missing presentation construction for stack cancellation. -/
def S2089StackPresentationStatement : Type 1 :=
  ∀ {X Y Z : EtaleStackOverField S1726K} (f : X.Hom Y) (g : Y.Hom Z),
    EtaleStackFiniteEtaleMorphism (Pseudofunctor.StrongTrans.vcomp f g) →
    EtaleStackFiniteEtaleMorphism g →
    ∀ (T : SchemeOverField S1726K)
      (ptY : Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber),
      EtaleStackBaseChangePresentation f T ptY

/-- Exact missing finite-etale property for the constructed presentation. -/
def S2089StackPropertyStatement : Prop :=
  ∀ {X Y Z : EtaleStackOverField S1726K} (f : X.Hom Y) (g : Y.Hom Z)
    (hf : EtaleStackFiniteEtaleMorphism (Pseudofunctor.StrongTrans.vcomp f g))
    (hg : EtaleStackFiniteEtaleMorphism g)
    (T : SchemeOverField S1726K)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber)
    (P : EtaleStackBaseChangePresentation f T ptY),
    AlgebraicGeometry.IsFinite P.projection.left ∧
      AlgebraicGeometry.Etale P.projection.left

/-- The presentation data and property give stack cancellation. -/
noncomputable def S2089StackCancellationOfPresentation
    (hpres : S2089StackPresentationStatement)
    (hprop : S2089StackPropertyStatement) : S2088StackCancellation := by
  intro X Y Z f g hfg hg
  refine { baseChange := ?_, hasProperty := ?_ }
  · intro T ptY
    exact hpres f g hfg hg T ptY
  · intro T ptY
    exact hprop f g hfg hg T ptY (hpres f g hfg hg T ptY)

#print axioms S2089StackCancellationOfPresentation

end LeanFormal.IUT.XiFPaper.S2089StackCancellationActual

end
