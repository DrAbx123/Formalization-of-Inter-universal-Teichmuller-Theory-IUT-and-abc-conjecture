import Mathlib
import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.Belyi
import tmp.sheaf.xif.paper.Mzk1Lemma24DescentActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24Descent2Actual

/-- **(D)-wiring**: a polynomial with rational coefficients is defined over any field
F of characteristic zero containing Q — it is the base change of a polynomial over F
(this is the coefficient-level content of the paper's "if S, beta are defined over F
then phi may be taken defined over F" for the rational Belyi maps produced by the
[TauCeti] Belyi machine). -/
theorem s3135_rational_polynomial_definedOver {F : Type*} [Field F] [Algebra ℚ F]
    (q : Polynomial ℚ) :
    ∃ qF : Polynomial F,
      qF.map (algebraMap F (AlgebraicClosure F)) =
        q.map (algebraMap ℚ (AlgebraicClosure F)) := by
  refine ⟨q.map (algebraMap ℚ F), ?_⟩
  rw [Polynomial.map_map]
  congr 1

/-- **(D)-wiring for the Belyi maps**: the TauCeti Belyi polynomial B_{m,n} over Q is
defined over every number field F (explicit base-changed polynomial). -/
theorem s3135_belyiPolynomial_definedOver {F : Type*} [Field F] [Algebra ℚ F]
    (m n : Nat) :
    ∃ qF : Polynomial F,
      qF.map (algebraMap F (AlgebraicClosure F)) =
        (TauCeti.belyiPolynomial ℚ m n).map
          (algebraMap ℚ (AlgebraicClosure F)) :=
  s3135_rational_polynomial_definedOver (TauCeti.belyiPolynomial ℚ m n)

/-- (D)-wiring status: rational (and Belyi) polynomials are defined over every number
field; the remaining descent items are the Galois-stability of S/beta and the
rational-function language. -/
def s3135Mzk1Descent2Status : Audit.Obligation :=
  { id := "MZK1.lemma24.descent.wiring"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 159-160"
    status := Audit.VerificationStatus.interface
    note := "PROVED: s3135_rational_polynomial_definedOver (any q in Q[X] is a base change from F[X] into Qbar[X]) and s3135_belyiPolynomial_definedOver (TauCeti B_{m,n} defined over every number field F). TOGETHER WITH Mzk1Lemma24DescentActual: finite-Galois scalar/coefficient descent PROVED; algebraic-closure infinite case registered as AlgebraicClosureFixedFieldPaperInput. REMAINING (D): Galois-stability of S and beta over F, and the rational-function representative/equality-of-maps language (P^1), named. Registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.descent", "MZK1.lemma24.main-statement" ]
    sorryItems := [ "Galois-stability of S and beta over F", "rational-function/P^1 representative language" ] }

#check s3135_rational_polynomial_definedOver
#check s3135_belyiPolynomial_definedOver
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24Descent2Actual
end