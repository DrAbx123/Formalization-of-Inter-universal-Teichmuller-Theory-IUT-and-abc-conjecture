import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind1Reduction

/-!
# Ind1/Ind2/Ind3 object reference (green Theorem311Source Ind1 reduction)

Reuses the green `Ind1Reduction.lean`: the (Ind1) formal quotient `Ind1Setoid`,
the quotient projection `ind1QuotientMap`, and the canonical descent data
`ind1DescentDataCanonical` with its consumer theorem `ind1DescentData_descends`.
These are the (Ind1) objects of the Theorem 3.11 multiradial output (IUT III
Theorem 3.11(i), Remark 3.11.1(i)).

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Ind123ObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

noncomputable section

universe u v

section Ind1

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]

/-- (Ind1) formal quotient setoid (orbits of the `ind1` action). -/
abbrev ind1Setoid (I : Input Label Choice) : Setoid Choice := Ind1Setoid I

/-- Canonical projection to the (Ind1) formal quotient. -/
def ind1Proj (I : Input Label Choice) : Choice → Quotient (Ind1Setoid I) :=
  ind1QuotientMap I

/-- Canonical (Ind1) descent data (formal quotient + descent of the
indeterminacy quotient through it). -/
def ind1Descent (I : Input Label Choice) : Ind1DescentData I :=
  ind1DescentDataCanonical I

/-- Consumer extraction: Ind1-related choices have the same quotient image. -/
theorem ind1_descent_descends (I : Input Label Choice) (D : Ind1DescentData I)
    {a b : Choice} (h : Ind1Relation I a b) :
    quotientMap I a = quotientMap I b :=
  ind1DescentData_descends I D h

end Ind1

end

end LeanFormal.IUT.XiFPaper.Mzk1Ind123ObjectActual
