import Mathlib.Data.Real.Basic
import LeanFormal.IUT.Foundations.Arithmetic.FiniteLabels
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv

/-! # S694: paper theta-average labels and weights

Source: IUT II Remark 4.7.3: volumes at j in F_l^x are weighted by 1/l*;
IUT III Theorem B/Cor 3.12 averages over j in F_l^x (l* labels, signs
identified).  Theta value at j is q[2u]^(j^2) = q[1u]^(j^2/(2l)).
This file records the label count and weight normalization only. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S694ThetaAverageNormalizationActual
open LeanFormal.IUT

variable {l : PrimeGeFive}

/-- The paper theta labels are the l* classes of F_l^x, j = 1,...,l*. -/
abbrev PaperThetaLabel (l : PrimeGeFive) : Type := Fin (lStar l.value)

/-- Paper weight: 1/l* at each theta label. -/
noncomputable def paperThetaLabelWeight (l : PrimeGeFive) : Real :=
  (lStar l.value : Real)⁻¹

/-- The paper procession average over the l* theta labels. -/
noncomputable def paperThetaLabelAverage
    (f : PaperThetaLabel l → Real) : Real :=
  paperThetaLabelWeight l * ∑ i : PaperThetaLabel l, f i

/-- The paper theta-label weights sum to one. -/
theorem paperThetaLabelWeight_sum :
    (∑ _ : PaperThetaLabel l, paperThetaLabelWeight l) = 1 := by
  unfold paperThetaLabelWeight
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hpos : (0 : Nat) < lStar l.value := by
    have h5 := l.ge_five
    unfold lStar
    omega
  have hne : (lStar l.value : Real) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hpos
  exact mul_inv_cancel₀ hne

/-- The old uniform SignedLabel weight, for comparison. -/
noncomputable def uniformSignedLabelWeight (l : PrimeGeFive) : Real :=
  (Fintype.card (SignedLabel l.value) : Real)⁻¹

/-- The uniform SignedLabel weight is 1/l, not 1/l*. -/
theorem uniformSignedLabelWeight_eq (l : PrimeGeFive) :
    uniformSignedLabelWeight l = (l.value : Real)⁻¹ := by
  unfold uniformSignedLabelWeight
  rw [SignedLabel.card_signedLabel]

/-- Correct ratio: paper weight / uniform SignedLabel weight = l / l*. -/
theorem paperThetaLabelWeight_eq_ratio (l : PrimeGeFive) :
    paperThetaLabelWeight l =
      (l.value : Real) / (lStar l.value : Real) * uniformSignedLabelWeight l := by
  unfold paperThetaLabelWeight uniformSignedLabelWeight
  rw [SignedLabel.card_signedLabel]
  have hpos : (0 : Nat) < lStar l.value := by
    have h5 := l.ge_five
    unfold lStar
    omega
  have hne : (lStar l.value : Real) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hpos
  have hl : (l.value : Real) ≠ 0 := by
    exact_mod_cast l.prime.ne_zero
  field_simp [hne, hl]

end LeanFormal.IUT.XiFPaper.S694ThetaAverageNormalizationActual
end