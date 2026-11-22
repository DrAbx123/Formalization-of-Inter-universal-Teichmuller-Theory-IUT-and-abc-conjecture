import Mathlib
import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.Belyi
import tmp.sheaf.xif.paper.Mzk1Lemma24MainStatementActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24BelyiConsumeActual

open LeanFormal.IUT.XiFPaper.Mzk1Lemma24MainStatementActual

/-- **Explicit Belyi map from the ported TauCeti asset**: the polynomial B_{1,1} = 4X(1-X)
is nonconstant (degree 2), maps 0 and 1 to 0, and its critical values over Qbar lie in
{0,1}.  Thus for S_phi = {0,1,infinity} it is a polynomial Belyi map of P^1 branched only
over S_phi — the object language for [Mzk1] Lemma 2.4. -/
theorem s3135_belyiPolynomial_1_1_data :
    (TauCeti.belyiPolynomial ℚ 1 1).natDegree = 2 ∧
    (TauCeti.belyiPolynomial ℚ 1 1).eval 0 = 0 ∧
    (TauCeti.belyiPolynomial ℚ 1 1).eval 1 = 0 ∧
    ((TauCeti.belyiPolynomial ℚ 1 1).criticalValues Qbar ⊆ ({0, 1} : Set Qbar)) := by
  refine ⟨by simp, by simp, by simp, ?_⟩
  exact TauCeti.criticalValues_belyiPolynomial_subset Qbar 1 1

/-- **TauCeti Belyi machinery re-exported for the (M) route**: the critical points of
B_{m,n} lie in {0,1,m/(m+n)} (explicit critical-set control). -/
theorem s3135_belyiPolynomial_criticalPoints_subset (L : Type*) [Field L] [Algebra ℚ L]
    (m n : Nat) :
    (Polynomial.derivative (TauCeti.belyiPolynomial ℚ m n)).rootSet L ⊆
      ({0, 1, (m : L) / (m + n)} : Set L) :=
  TauCeti.rootSet_derivative_belyiPolynomial_subset L m n

#check s3135_belyiPolynomial_1_1_data
#check s3135_belyiPolynomial_criticalPoints_subset
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24BelyiConsumeActual
end
