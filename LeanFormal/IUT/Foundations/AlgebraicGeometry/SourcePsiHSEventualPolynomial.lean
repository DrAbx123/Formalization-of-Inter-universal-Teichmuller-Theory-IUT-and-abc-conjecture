/-
  Eventual polynomial and leading coefficient for the actual Hilbert function.

  The actual length function n -> length(A_q / m_q^n) is available.  Mathlib
  supplies polynomials and filter-eventually predicates, but no Hilbert-Samuel
  multiplicity or eventual-polynomial existence theorem.  This file therefore
  defines eventual-polynomial data conditionally and proves uniqueness of the
  polynomial, its degree and its leading coefficient from eventual agreement.
  The multiplicity is d! times the leading coefficient; it is actual only when the
  eventual-polynomial datum exists.  No multiplicity value is fabricated.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiHSMultiplicityActual
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Filter.AtTopBot

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiHSEventualPolynomial

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiActualSpecialFiber
open LeanFormal.IUT.SourcePsiComponentFiniteActual
open LeanFormal.IUT.SourcePsiComponentIntersectionGraph
open LeanFormal.IUT.SourcePsiNodeCuspMultiplicity
open LeanFormal.IUT.SourcePsiHilbertSamuelMultiplicity
open LeanFormal.IUT.SourcePsiHSMultiplicityActual
open Filter

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- Candidate Jacobian prime. -/
abbrev SourcePsiHSCandidatePrime : Type u :=
  SourcePsiHSCandidatePrime S v

/-- Actual local ring. -/
abbrev SourcePsiHSLocalRing (q : SourcePsiHSCandidatePrime S v) : Type u :=
  SourcePsiHSLocalRing S v q

/-- Actual length function. -/
abbrev SourcePsiHSLength (q : SourcePsiHSCandidatePrime S v) (n : ℕ) : ℕ∞ :=
  SourcePsiHSLength S v q n

/-- Eventual agreement of the actual rational length function with a polynomial. -/
def SourcePsiHSEventuallyEq
    (q : SourcePsiHSCandidatePrime S v) (P : Polynomial ℚ) : Prop :=
  ∀ᶠ n in atTop, (SourcePsiHSLength S v q n : ℚ) = P.eval (n : ℚ)

/-- Eventual polynomial data: a polynomial, its degree, and eventual agreement
with the actual length function.  No inhabitant is asserted. -/
structure SourcePsiHSEventualPolynomialData
    (q : SourcePsiHSCandidatePrime S v) where
  degree : ℕ
  polynomial : Polynomial ℚ
  polynomial_natDegree : polynomial.natDegree = degree
  eventually_eq : SourcePsiHSEventuallyEq S v q polynomial

/-- The eventual polynomial associated to the data. -/
abbrev SourcePsiHSEventualPolynomial
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSEventualPolynomialData S v q) : Polynomial ℚ :=
  D.polynomial

/-- Degree of the eventual polynomial. -/
abbrev SourcePsiHSEventualDegree
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSEventualPolynomialData S v q) : ℕ :=
  D.degree

/-- Leading coefficient of the eventual polynomial. -/
def SourcePsiHSEventualLeadingCoefficient
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSEventualPolynomialData S v q) : ℚ :=
  D.polynomial.leadingCoeff

/-- Eventual Hilbert-Samuel multiplicity: d! times the eventual leading
coefficient. -/
def SourcePsiHSEventualMultiplicity
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSEventualPolynomialData S v q) : ℚ :=
  (Nat.factorial D.degree : ℚ) *
    SourcePsiHSEventualLeadingCoefficient S v q D

/-- The eventual polynomial relation at each level is the actual length function. -/
theorem SourcePsiHSEventualPolynomial_eval
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSEventualPolynomialData S v q) :
    ∀ᶠ n in atTop,
      (SourcePsiHSLength S v q n : ℚ) = D.polynomial.eval (n : ℚ) :=
  D.eventually_eq

/-- Eventual polynomial uniqueness from eventual agreement with the same actual
length function. -/
theorem SourcePsiHSEventualPolynomial_unique
    (q : SourcePsiHSCandidatePrime S v)
    (P Q : Polynomial ℚ)
    (hP : SourcePsiHSEventuallyEq S v q P)
    (hQ : SourcePsiHSEventuallyEq S v q Q) :
    P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have h : ∀ᶠ n in atTop, P.eval (n : ℚ) = Q.eval (n : ℚ) := by
    filter_upwards [hP, hQ] with n hnP hnQ
    exact hnP.symm.trans hnQ
  have hset : Set.Infinite {n : ℕ | P.eval (n : ℚ) = Q.eval (n : ℚ)} := by
    exact h.exists_forall_of_atTop.finite_or_infinite.resolve_left ?_
  · exact hset
  · intro hfin
    exact not_finite_atTop (hfin.subset (by intro n hn; exact hn))

/-- Uniqueness of the eventual polynomial from two data records. -/
theorem SourcePsiHSEventualPolynomialData_unique
    (q : SourcePsiHSCandidatePrime S v)
    (D₁ D₂ : SourcePsiHSEventualPolynomialData S v q) :
    D₁.polynomial = D₂.polynomial :=
  SourcePsiHSEventualPolynomial_unique S v q D₁.polynomial D₂.polynomial
    D₁.eventually_eq D₂.eventually_eq

/-- Uniqueness of the eventual degree. -/
theorem SourcePsiHSEventualDegree_unique
    (q : SourcePsiHSCandidatePrime S v)
    (D₁ D₂ : SourcePsiHSEventualPolynomialData S v q) :
    D₁.degree = D₂.degree := by
  rw [← D₁.polynomial_natDegree, ← D₂.polynomial_natDegree,
    SourcePsiHSEventualPolynomialData_unique S v q D₁ D₂]

/-- Uniqueness of the eventual leading coefficient. -/
theorem SourcePsiHSEventualLeadingCoefficient_unique
    (q : SourcePsiHSCandidatePrime S v)
    (D₁ D₂ : SourcePsiHSEventualPolynomialData S v q) :
    SourcePsiHSEventualLeadingCoefficient S v q D₁ =
      SourcePsiHSEventualLeadingCoefficient S v q D₂ := by
  rw [SourcePsiHSEventualLeadingCoefficient,
    SourcePsiHSEventualLeadingCoefficient,
    SourcePsiHSEventualPolynomialData_unique S v q D₁ D₂]

/-- Uniqueness of the eventual multiplicity value. -/
theorem SourcePsiHSEventualMultiplicity_unique
    (q : SourcePsiHSCandidatePrime S v)
    (D₁ D₂ : SourcePsiHSEventualPolynomialData S v q) :
    SourcePsiHSEventualMultiplicity S v q D₁ =
      SourcePsiHSEventualMultiplicity S v q D₂ := by
  unfold SourcePsiHSEventualMultiplicity
  rw [SourcePsiHSEventualDegree_unique S v q D₁ D₂,
    SourcePsiHSEventualLeadingCoefficient_unique S v q D₁ D₂]

/-- Conversion from the threshold-style eventual data in the HS multiplicity file
to filter-eventual data. -/
def SourcePsiHSEventualPolynomialData.ofMultiplicityData
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSMultiplicityData S v q) :
    SourcePsiHSEventualPolynomialData S v q where
  degree := D.degree
  polynomial := D.polynomial
  polynomial_natDegree := D.polynomial_natDegree
  eventually_eq := by
    exact eventually_atTop.mpr ⟨D.threshold, by
      intro n hn
      exact D.eventual_length n hn⟩

/-- The eventual multiplicity from converted data is factorial times the
leading coefficient. -/
theorem SourcePsiHSEventualMultiplicity_ofMultiplicityData
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSMultiplicityData S v q) :
    SourcePsiHSEventualMultiplicity S v q
        (SourcePsiHSEventualPolynomialData.ofMultiplicityData S v q D) =
      (Nat.factorial D.degree : ℚ) * D.polynomial.leadingCoeff :=
  rfl

/-- Positive eventual multiplicity under positive eventual leading coefficient. -/
theorem SourcePsiHSEventualMultiplicity_pos
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSEventualPolynomialData S v q)
    (h : 0 < SourcePsiHSEventualLeadingCoefficient S v q D) :
    0 < SourcePsiHSEventualMultiplicity S v q D := by
  unfold SourcePsiHSEventualMultiplicity
  have hfac : (0 : ℚ) < (Nat.factorial D.degree : ℚ) := by
    exact_mod_cast Nat.factorial_pos D.degree
  exact mul_pos hfac h

/-- Nonnegative eventual multiplicity under nonnegative leading coefficient. -/
theorem SourcePsiHSEventualMultiplicity_nonneg
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSEventualPolynomialData S v q)
    (h : 0 ≤ SourcePsiHSEventualLeadingCoefficient S v q D) :
    0 ≤ SourcePsiHSEventualMultiplicity S v q D := by
  unfold SourcePsiHSEventualMultiplicity
  exact mul_nonneg (by positivity) h

/-- The leading coefficient of a nonzero eventual polynomial is nonzero. -/
theorem SourcePsiHSEventualLeadingCoefficient_ne_zero
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSEventualPolynomialData S v q)
    (h : D.polynomial ≠ 0) :
    SourcePsiHSEventualLeadingCoefficient S v q D ≠ 0 :=
  Polynomial.leadingCoeff_ne_zero.mpr h

/-- Degree bound from eventual agreement if the polynomial is known: the degree
is the natDegree of the eventual polynomial. -/
theorem SourcePsiHSEventualDegree_eq_natDegree
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSEventualPolynomialData S v q) :
    D.degree = D.polynomial.natDegree :=
  D.polynomial_natDegree.symm

/-- The eventual polynomial at sufficiently large n is the actual rational
length. -/
theorem SourcePsiHSEventualPolynomial_eventually
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSEventualPolynomialData S v q) :
    ∀ᶠ n in atTop,
      (SourcePsiHSLength S v q n : ℚ) =
        SourcePsiHSEventualPolynomial S v q D |>.eval (n : ℚ) :=
  D.eventually_eq

/-- Exact eventual-polynomial residual: existence of the data and the geometric
node/cusp/component residual.  No eventual polynomial or multiplicity value is
asserted without the data. -/
def SourcePsiHSEventualPolynomialResidual : Prop :=
  (∀ q : SourcePsiHSCandidatePrime S v,
    Nonempty (SourcePsiHSEventualPolynomialData S v q)) ∧
    SourcePsiHSGeometricResidual S v

/-- The eventual-polynomial data is separate from the geometric residual; no
unconditional existence is asserted. -/
theorem SourcePsiHSEventualPolynomialResidual_geometric
    (h : SourcePsiHSEventualPolynomialResidual S v) :
    SourcePsiHSGeometricResidual S v :=
  h.2



/-- Eventual equality is stable under equality of polynomials. -/
theorem SourcePsiHSEventuallyEq_of_eq
    (q : SourcePsiHSCandidatePrime S v)
    {P Q : Polynomial ℚ} (h : P = Q)
    (hP : SourcePsiHSEventuallyEq S v q P) :
    SourcePsiHSEventuallyEq S v q Q := by
  rwa [← h]

/-- The eventual polynomial relation is the same as eventual equality of rational
length values. -/
theorem SourcePsiHSEventualEq_iff {q : SourcePsiHSCandidatePrime S v}
    {P : Polynomial ℚ} :
    SourcePsiHSEventuallyEq S v q P ↔
      ∀ᶠ n in atTop, (SourcePsiHSLength S v q n : ℚ) = P.eval (n : ℚ) :=
  Iff.rfl

/-- The converted multiplier data has the same polynomial. -/
theorem SourcePsiHSEventualData_ofMultiplicityData_polynomial
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSMultiplicityData S v q) :
    (SourcePsiHSEventualPolynomialData.ofMultiplicityData S v q D).polynomial =
      D.polynomial :=
  rfl

/-- The converted data has the same degree. -/
theorem SourcePsiHSEventualData_ofMultiplicityData_degree
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSMultiplicityData S v q) :
    (SourcePsiHSEventualPolynomialData.ofMultiplicityData S v q D).degree =
      D.degree :=
  rfl

/-- The converted data eventually agrees with the actual length. -/
theorem SourcePsiHSEventualData_ofMultiplicityData_eventually
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSMultiplicityData S v q) :
    SourcePsiHSEventuallyEq S v q D.polynomial :=
  (SourcePsiHSEventualPolynomialData.ofMultiplicityData S v q D).eventually_eq

/-- Two eventual data records with the same polynomial have the same leading
coefficient. -/
theorem SourcePsiHSEventualLeadingCoefficient_congr
    (q : SourcePsiHSCandidatePrime S v)
    (D₁ D₂ : SourcePsiHSEventualPolynomialData S v q)
    (h : D₁.polynomial = D₂.polynomial) :
    SourcePsiHSEventualLeadingCoefficient S v q D₁ =
      SourcePsiHSEventualLeadingCoefficient S v q D₂ := by
  simp [SourcePsiHSEventualLeadingCoefficient, h]

/-- The eventual multiplicity is factorial times the leading coefficient,
consumer form. -/
theorem SourcePsiHSEventualMultiplicity_eq_factorial
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSEventualPolynomialData S v q) :
    SourcePsiHSEventualMultiplicity S v q D =
      (Nat.factorial D.degree : ℚ) * D.polynomial.leadingCoeff :=
  rfl

/-- A positive eventual leading coefficient remains nonzero. -/
theorem SourcePsiHSEventualLeadingCoefficient_ne_zero_of_pos
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSEventualPolynomialData S v q)
    (h : 0 < SourcePsiHSEventualLeadingCoefficient S v q D) :
    SourcePsiHSEventualLeadingCoefficient S v q D ≠ 0 :=
  ne_of_gt h

/-- Nonzero eventual multiplicity under positive leading coefficient. -/
theorem SourcePsiHSEventualMultiplicity_ne_zero_of_pos
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSEventualPolynomialData S v q)
    (h : 0 < SourcePsiHSEventualLeadingCoefficient S v q D) :
    SourcePsiHSEventualMultiplicity S v q D ≠ 0 :=
  ne_of_gt (SourcePsiHSEventualMultiplicity_pos S v q D h)

/-- Existence of threshold-style HS data gives existence of eventual-polynomial
data. -/
theorem SourcePsiHSEventualPolynomialData_nonempty_of_multiplicityData
    (q : SourcePsiHSCandidatePrime S v)
    (h : Nonempty (SourcePsiHSMultiplicityData S v q)) :
    Nonempty (SourcePsiHSEventualPolynomialData S v q) :=
  h.imp (SourcePsiHSEventualPolynomialData.ofMultiplicityData S v q)

/-- API obstruction statement: eventual-polynomial data is the missing input;
the actual length function and geometric residual are separate. -/
def SourcePsiHSEventualPolynomialAPIResidual : Prop :=
  (∀ q : SourcePsiHSCandidatePrime S v,
    Nonempty (SourcePsiHSEventualPolynomialData S v q)) ∧
    SourcePsiHSGeometricResidual S v

/-- The API residual is exactly the eventual-polynomial existence and geometric
residual. -/
theorem SourcePsiHSEventualPolynomialAPIResidual_iff
    (h : SourcePsiHSEventualPolynomialAPIResidual S v) :
    SourcePsiHSEventualPolynomialResidual S v :=
  ⟨h.1, h.2⟩

/-- Geometric residual is present independently of eventual-polynomial
existence. -/
theorem SourcePsiHSEventualGeometricResidual_iff :
    SourcePsiHSGeometricResidual S v :=
  SourcePsiHSGeometricResidual_iff S v

/-! ## Exact eventual-polynomial boundary

Constructed:
- filter-eventual agreement of the actual rational length function with a
  polynomial;
- eventual-polynomial data structure with degree and natDegree compatibility;
- eventual leading coefficient and d! times leading coefficient multiplicity;
- uniqueness of the polynomial, degree, leading coefficient and multiplicity
  from eventual agreement;
- conversion from threshold-style HS data to filter-eventual data;
- positivity/nonnegativity under sign conditions;
- exact residual separating eventual-polynomial existence from geometric data.

NOT asserted:
- existence of eventual-polynomial data;
- an unconditional Hilbert-Samuel multiplicity value;
- geometric node/cusp/component multiplicity;
- stable/source comparison.

No multiplicity value is fabricated.
-/
end LeanFormal.IUT.SourcePsiHSEventualPolynomial

end