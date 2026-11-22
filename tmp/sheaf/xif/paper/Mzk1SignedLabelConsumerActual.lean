import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv
import LeanFormal.IUT.Foundations.Theta.GaussianKernel

/-!
# Mzk1SignedLabelConsumerActual — consumer theorems over the tree signed-label assets
(SignedLabelEquiv / GaussianKernel, OLEAN_FRESH). Composed projections only.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1SignedLabelConsumerActual

open LeanFormal.IUT
open scoped BigOperators

/-- Consumer: signed labels at l >= 5 have exactly l elements. -/
theorem consumer_card_signedLabel (l : PrimeGeFive) :
    Fintype.card (SignedLabel l.value) = l.value :=
  card_signedLabel l

/-- Consumer: translation permutes a sum over signed labels. -/
theorem consumer_sum_translate (l : PrimeGeFive) (t : Fl l.value)
    (f : SignedLabel l.value → ℝ) :
    ∑ j, f (translate l t j) = ∑ j, f j :=
  sum_translate l t f

/-- Consumer: the signed-label/finite-label equivalence is bijective. -/
theorem consumer_equiv_bijective (l : PrimeGeFive) :
    Function.Bijective (equiv l) :=
  (equiv l).bijective

/-- Consumer: translating by -t is inverse to translating by t. -/
theorem consumer_translate_inverse (l : PrimeGeFive) (t : Fl l.value)
    (j : SignedLabel l.value) : translate l (-t) (translate l t j) = j :=
  translate_inverse l t j

#check consumer_card_signedLabel
#check consumer_sum_translate
#check consumer_equiv_bijective
#check consumer_translate_inverse

end LeanFormal.IUT.XiFPaper.Mzk1SignedLabelConsumerActual
end
