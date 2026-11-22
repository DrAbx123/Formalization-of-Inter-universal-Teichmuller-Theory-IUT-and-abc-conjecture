import Mathlib
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24DescentActual

/-- **Finite Galois scalar descent** (used for [Mzk1] Lemma 2.4 lines 159-160): an
element of a finite Galois extension fixed by every F-automorphism lies in the base
field.  Proof via the Galois fixed-field theorem. -/
theorem s3135_descent_finite_galois {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (x : E)
    (hx : ∀ σ : E ≃ₐ[F] E, σ x = x) : ∃ f : F, algebraMap F E f = x := by
  have hmem : x ∈ IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E)) := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    exact hx σ
  rw [IsGalois.fixedField_top] at hmem
  exact IntermediateField.mem_bot.mp hmem

/-- **Finite Galois coefficient descent**: if a polynomial over a finite Galois
extension is fixed by every F-automorphism, then each of its coefficients lies in the
base field (each coefficient is Galois-fixed). -/
theorem s3135_coeff_descent_finite_galois {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (p : Polynomial E)
    (hfix : ∀ σ : E ≃ₐ[F] E, p.map σ.toAlgHom.toRingHom = p) (n : Nat) :
    ∃ c : F, algebraMap F E c = p.coeff n := by
  have hx : ∀ σ : E ≃ₐ[F] E, σ (p.coeff n) = p.coeff n := by
    intro σ
    have h := congrArg (fun q : Polynomial E => q.coeff n) (hfix σ)
    simpa [Polynomial.coeff_map] using h
  exact s3135_descent_finite_galois (p.coeff n) hx

/-- **Paper-input registration (D)**: descent over the algebraic closure of a number
field F (paper [Mzk1] Lemma 2.4 lines 159-160: if S, beta are defined over F then phi
may be taken to be defined over F).  Mathematical content at coefficient level: an
element of the algebraic closure fixed by every F-automorphism lies in F.  Standard
infinite Galois theory; registered explicitly as a paper input because the pinned
Mathlib fixed-field API used in this file is the finite-dimensional Galois one. -/
def AlgebraicClosureFixedFieldPaperInput (F : Type) [Field F] : Prop :=
  ∀ x : AlgebraicClosure F,
    (∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, σ x = x) →
      ∃ f : F, algebraMap F (AlgebraicClosure F) f = x

/-- Conditional algebraic-closure coefficient descent from the registered paper input:
the paper's "defined over F" assertion for the coefficients of a Galois-stable
polynomial over Qbar. -/
theorem s3135_coeff_descent_algebraicClosure_of_paperInput {F : Type} [Field F]
    (hD : AlgebraicClosureFixedFieldPaperInput F)
    (p : Polynomial (AlgebraicClosure F))
    (hfix : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
      p.map σ.toAlgHom.toRingHom = p) (n : Nat) :
    ∃ c : F, algebraMap F (AlgebraicClosure F) c = p.coeff n := by
  have hx : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
      σ (p.coeff n) = p.coeff n := by
    intro σ
    have h := congrArg (fun q : Polynomial (AlgebraicClosure F) => q.coeff n) (hfix σ)
    simpa [Polynomial.coeff_map] using h
  exact hD (p.coeff n) hx

/-- (D) status: finite Galois descent PROVED (scalar and coefficient level); the
infinite (algebraic closure) case is reduced to the exact named paper input, and the
remaining wiring is "Galois-stable rational function over Qbar has a representative
defined over F" (needs the rational-function language). -/
def s3135Mzk1DescentStatus : Audit.Obligation :=
  { id := "MZK1.lemma24.descent"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 159-160"
    status := Audit.VerificationStatus.interface
    note := "PROVED: s3135_descent_finite_galois (fixed by all F-automorphisms => in F; via IntermediateField.fixedField_top + mem_bot); s3135_coeff_descent_finite_galois (coefficient-level). REGISTERED class-B paper input: AlgebraicClosureFixedFieldPaperInput (infinite Galois fixed field over Qbar); conditional s3135_coeff_descent_algebraicClosure_of_paperInput. REMAINING wiring: from coefficient descent to phi defined over F (rational-function representative), which needs the P^1/rational-function language; named. No fake witnesses; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.f0-coefficient-bound" ]
    sorryItems :=
      [ "AlgebraicClosureFixedFieldPaperInput (infinite Galois fixed field)",
        "rational-function representative defined over F (P^1 language)" ] }

#check s3135_descent_finite_galois
#check s3135_coeff_descent_finite_galois
#check s3135_coeff_descent_algebraicClosure_of_paperInput
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24DescentActual
end