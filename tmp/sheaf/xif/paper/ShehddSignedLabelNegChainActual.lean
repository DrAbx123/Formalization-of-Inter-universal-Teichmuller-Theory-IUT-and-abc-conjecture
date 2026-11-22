import LeanFormal.IUT.Foundations.Theta.GaussianKernel

/-!
# ShehddSignedLabelNegChainActual — signed label negation / theta invariance chain

New chain consequences of the compiled signed-label negation and Gaussian theta laws: the
negation is involutive, the finite-label map is odd, and the real theta value is even.  No
new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddSignedLabelNegChainActual

open LeanFormal.IUT
open LeanFormal.IUT.SignedLabel

/-- **PROVED chain:** signed-label negation is involutive and the real theta value is even
under it. -/
theorem signedLabel_neg_theta_chain (l : Nat) (q : Real) (j : SignedLabel l) :
    SignedLabel.neg (SignedLabel.neg j) = j ∧
      realThetaValue q (SignedLabel.neg j).1 = realThetaValue q j.1 := by
  refine ⟨SignedLabel.neg_involutive j, ?_⟩
  exact SignedLabel.theta_neg q j

/-- **PROVED chain:** the finite-label map sends negation to negation. -/
theorem signedLabel_toFl_neg_chain (l : Nat) (j : SignedLabel l) :
    SignedLabel.toFl l (SignedLabel.neg j) = -SignedLabel.toFl l j :=
  SignedLabel.toFl_neg j

/-- **PROVED chain:** the negation value is the integer negation, and the Gaussian
exponent is even on it. -/
theorem signedLabel_neg_val_chain (l : Nat) (j : SignedLabel l) :
    (SignedLabel.neg j).1 = -j.1 ∧ gaussExponent (-j.1) = gaussExponent j.1 := by
  refine ⟨SignedLabel.neg_val j, ?_⟩
  simp

end LeanFormal.IUT.XiFPaper.ShehddSignedLabelNegChainActual
end
