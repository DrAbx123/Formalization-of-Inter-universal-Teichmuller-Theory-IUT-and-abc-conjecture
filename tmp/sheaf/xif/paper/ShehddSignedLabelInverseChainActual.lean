import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv

/-!
# ShehddSignedLabelInverseChainActual — signed-label dictionary inverse chain

New chain consequence of the compiled injectivity and representative laws: the bounded
integer representative is a right inverse of the finite-label dictionary.  No new
assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddSignedLabelInverseChainActual

open LeanFormal.IUT
open LeanFormal.IUT.SignedLabel

/-- **PROVED chain:** the representative of the finite-label dictionary value returns the
original signed label (right inverse; distinct from the compiled left inverse
`representative_toFl`). -/
theorem representative_toFiniteLabel (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    SignedLabel.representative l (SignedLabel.toFiniteLabel l j) = j :=
  SignedLabel.toFiniteLabel_injective l
    (SignedLabel.representative_toFl l (SignedLabel.toFiniteLabel l j))

/-- **PROVED chain:** the finite-label dictionary is a bijection between signed labels and
their image, with the representative as inverse. -/
theorem toFiniteLabel_bijective_chain (l : PrimeGeFive) :
    Function.Injective (SignedLabel.toFiniteLabel l) ∧
      Function.LeftInverse (SignedLabel.toFiniteLabel l) (SignedLabel.representative l) :=
  ⟨SignedLabel.toFiniteLabel_injective l,
    fun x => SignedLabel.representative_toFl l x⟩

end LeanFormal.IUT.XiFPaper.ShehddSignedLabelInverseChainActual
end