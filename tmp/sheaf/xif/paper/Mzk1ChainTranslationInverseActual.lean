import tmp.sheaf.xif.paper.Mzk1ChainTranslationLawActual

/-!
# Mzk1ChainTranslationInverseActual — derived inverse/injectivity laws for the chain
translation action (new theorems from the existing translation-law asset; no copies).
No axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainTranslationInverseActual

open LeanFormal.IUT

/-- Derived: the inverse translation is a left inverse. -/
theorem chainTranslation_neg_mul (k : ℤ) :
    chainTranslation (-k) * chainTranslation k = 1 := by
  rw [← chainTranslation_add]
  simp

/-- Derived: the inverse translation is a right inverse. -/
theorem chainTranslation_mul_neg (k : ℤ) :
    chainTranslation k * chainTranslation (-k) = 1 := by
  rw [← chainTranslation_add]
  simp

/-- Derived: every chain translation is injective. -/
theorem chainTranslation_injective (k : ℤ) :
    Function.Injective (chainTranslation k) :=
  (chainTranslation k).injective

/-- Derived: every chain translation is bijective. -/
theorem chainTranslation_bijective (k : ℤ) :
    Function.Bijective (chainTranslation k) :=
  (chainTranslation k).bijective

#check chainTranslation_neg_mul
#check chainTranslation_mul_neg
#check chainTranslation_injective
#check chainTranslation_bijective

end LeanFormal.IUT.XiFPaper.Mzk1ChainTranslationInverseActual
end
