import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv

/-!
# Mzk1SignedLabelTranslateActual — derived laws for the signed-label translation action
(new theorems from the existing SignedLabelEquiv asset; no copies). No axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1SignedLabelTranslateActual

open LeanFormal.IUT

/-- Derived: translating by zero is the identity. -/
theorem translate_zero_apply (l : PrimeGeFive) (j : SignedLabel l.value) :
    translate l 0 j = j := by
  apply (equiv l).injective
  rw [translate_apply, zero_add]

/-- Derived: translating by s and then applying the label equivalence. -/
theorem translate_apply_zero (l : PrimeGeFive) (t : Fl l.value)
    (j : SignedLabel l.value) :
    equiv l (translate l t j) = t + equiv l j :=
  translate_apply l t j

/-- Derived: translate by t followed by translate by -t is the identity. -/
theorem translate_comp_neg (l : PrimeGeFive) (t : Fl l.value)
    (j : SignedLabel l.value) : translate l (-t) (translate l t j) = j :=
  translate_inverse l t j

/-- Derived: translate by -t followed by translate by t is the identity. -/
theorem translate_comp_neg' (l : PrimeGeFive) (t : Fl l.value)
    (j : SignedLabel l.value) : translate l t (translate l (-t) j) = j :=
  translate_cancel l t j

#check translate_zero_apply
#check translate_apply_zero
#check translate_comp_neg
#check translate_comp_neg'

end LeanFormal.IUT.XiFPaper.Mzk1SignedLabelTranslateActual
end
