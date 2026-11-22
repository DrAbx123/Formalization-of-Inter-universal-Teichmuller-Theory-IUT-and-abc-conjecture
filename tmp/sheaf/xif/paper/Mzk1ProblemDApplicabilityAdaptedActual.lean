import Mathlib
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1ProblemDApplicabilityAdaptedActual
open CategoryTheory AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] {C : Scheme.{u}}
structure ProblemDApplicabilityData (C : Scheme.{u}) (T D : Set C) where
  finiteT : T.Finite
  closedT : IsClosed T
  genus : Nat
  finiteCard : Nat
  card_eq : finiteCard = T.ncard
  card_ge : 2 * genus + 1 <= finiteCard
  divisor_eq : D = T
theorem card_ge_of_data {T D : Set C} (data : ProblemDApplicabilityData C T D) :
    2 * data.genus + 1 <= data.finiteCard := data.card_ge
theorem divisor_eq_of_data {T D : Set C} (data : ProblemDApplicabilityData C T D) : D = T := data.divisor_eq
def ProblemDApplicabilityInput : Prop :=
  forall (T D : Set C), T.Finite -> IsClosed T -> Nonempty (ProblemDApplicabilityData C T D)
def problemDApplicabilityRows : List (String × String) :=
  [ ("ProblemDApplicabilityData (finiteT/closedT/genus/card_ge/divisor_eq)", "DEFINED"),
    ("ProblemDApplicabilityInput", "NAMED (existence not asserted)") ]
theorem problemDApplicabilityRows_length : problemDApplicabilityRows.length = 2 := rfl
#check ProblemDApplicabilityData
#check ProblemDApplicabilityInput
end LeanFormal.IUT.XiFPaper.Mzk1ProblemDApplicabilityAdaptedActual
end
