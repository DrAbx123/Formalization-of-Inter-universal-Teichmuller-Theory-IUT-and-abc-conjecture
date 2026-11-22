import tmp.sheaf.xif.paper.S1755TwoYonedaSmallnessActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1756QuotientActual

/-- Quotient of raw cover maps by 2-isomorphism. -/
abbrev S1756CoverMapQuot (A B : S1728Cover) : Type 1 :=
  Quot (fun f g : S1728CoverMap A B => S1728CoverMapRel f g)

/-- Exact well-definedness premise for descending the extraction to the
quotient: 2-isomorphic cover maps must have equal extracted model homs. -/
def S1756LiftWellDefined : Prop :=
  forall (A B : S1728Cover) (f g : S1728CoverMap A B),
    S1728CoverMapRel f g ->
      S1755ModelHomOfCoverMap A B f = S1755ModelHomOfCoverMap A B g

/-- The descended extraction. -/
noncomputable def S1756QuotToModel
    (h : S1756LiftWellDefined) (A B : S1728Cover) :
    S1756CoverMapQuot A B -> (S1733Model A ⟶ S1733Model B) :=
  Quot.lift (S1755ModelHomOfCoverMap A B)
    (fun f g hr => h A B f g hr)

/-- Injectivity on the quotient, from S1755's faithfulness on 2-iso
classes. -/
theorem S1756QuotToModel_injective
    (h : S1756LiftWellDefined) (A B : S1728Cover) :
    Function.Injective (S1756QuotToModel h A B) := by
  intro q1 q2 heq
  induction q1 using Quot.ind with
  | _ f =>
    induction q2 using Quot.ind with
    | _ g =>
      apply Quot.sound
      exact S1755CoverMapRel_of_modelHom_eq heq

/-- Surjectivity on the quotient is exactly the missing inverse data. -/
def S1756QuotSurjective (h : S1756LiftWellDefined) : Prop :=
  forall A B : S1728Cover,
    Function.Surjective (S1756QuotToModel h A B)

#print axioms S1756QuotToModel_injective

end LeanFormal.IUT.XiFPaper.S1756QuotientActual
end
