import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv

noncomputable section

namespace LeanFormal.IUT.XiFPaper.SignedLabelOneActual

open LeanFormal.IUT

theorem lStar_ge_one (l : PrimeGeFive) : 1 ≤ lStar l.value := by
  have h := l.ge_five
  unfold lStar
  omega

/-- The signed label `1`. -/
def oneLabel (l : PrimeGeFive) : SignedLabel l.value := ⟨1, by
  change -(lStar l.value : Int) ≤ (1 : Int) ∧ (1 : Int) ≤ (lStar l.value : Int)
  constructor
  · have h := lStar_ge_one l
    omega
  · have h := lStar_ge_one l
    omega⟩

theorem oneLabel_val (l : PrimeGeFive) : (oneLabel l).1 = 1 := rfl

theorem gaussExponent_oneLabel (l : PrimeGeFive) :
    (gaussExponent (oneLabel l).1).toNat = 1 := by
  rw [oneLabel_val]
  norm_num [gaussExponent]

end LeanFormal.IUT.XiFPaper.SignedLabelOneActual

end
