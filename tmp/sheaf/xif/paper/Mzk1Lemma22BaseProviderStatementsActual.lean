import tmp.sheaf.xif.paper.RestatedLemma22InterfaceActual
import tmp.sheaf.xif.paper.Mzk1GChoiceScaleActual
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import tmp.sheaf.xif.paper.Mzk1Lemma22BaseGoodActual

/-! # Mzk1Lemma22BaseProviderStatementsActual — statement layer for the 2.2 base provider

Real Lean statements (no sorry/axiom): the base-provider objects of the flat Good
induction for [Mzk1] Lemma 2.2 (F=Q component): existence of a Good polynomial for
|S| <= 3 under the paper hypotheses, and its equivalence with the existing proved
base case (baseGood_exists in Mzk1Lemma22BaseGoodActual).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22BaseProviderStatementsActual

open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22BaseGoodActual

attribute [local instance] Classical.decEq

/-- Paper object: base provider statement for |S| <= 3. -/
def BaseGoodProviderStatement : Prop :=
  forall (S : Finset (P1Point Rat)) (beta : P1Point Rat),
    S.card <= 3 -> Lemma22Hypotheses S beta -> exists f : Polynomial Rat, Good f S beta

/-- The statement is realised by the PROVED base case (pointwise equivalence). -/
theorem baseGoodProviderStatement_of_baseGood (S : Finset (P1Point Rat))
    (beta : P1Point Rat) (hcard : S.card <= 3) (H : Lemma22Hypotheses S beta) :
    exists f : Polynomial Rat, Good f S beta :=
  baseGood_exists S beta H hcard

/-- Row record. -/
def baseProviderRows : List (String × String) :=
  [ ("BaseGoodProviderStatement (|S|<=3 Good)", "STATEMENT; realised by baseGood_exists (PROVED)") ]

theorem baseProviderRows_length : baseProviderRows.length = 1 := rfl

#check BaseGoodProviderStatement
#check baseGoodProviderStatement_of_baseGood

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22BaseProviderStatementsActual
end
