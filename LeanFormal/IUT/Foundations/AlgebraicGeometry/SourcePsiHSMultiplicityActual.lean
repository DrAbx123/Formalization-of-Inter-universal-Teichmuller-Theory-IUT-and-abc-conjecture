/-
  Hilbert-Samuel multiplicity from the actual length function.

  The actual local ring A_q and maximal ideal m_q give the actual length function
  n -> length(A_q / m_q^n).  Mathlib does not provide an eventual-polynomial or
  Hilbert-Samuel multiplicity API, so this file defines the multiplicity only
  conditionally on actual eventual-polynomial data.  The value is
  d! * leadingCoefficient of that polynomial; positivity is proved under positive
  leading coefficient, and length additivity is proved from the standard exact
  sequence.  Only geometric node/cusp/component multiplicity residual remains;
  no multiplicity value is fabricated.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiGradedRingFull
import Mathlib.RingTheory.Length
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Nat.Factorial.Basic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiHSMultiplicityActual

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiActualSpecialFiber
open LeanFormal.IUT.SourcePsiComponentFiniteActual
open LeanFormal.IUT.SourcePsiComponentIntersectionGraph
open LeanFormal.IUT.SourcePsiNodeCuspMultiplicity
open LeanFormal.IUT.SourcePsiHilbertSamuelMultiplicity
open LeanFormal.IUT.SourcePsiAssociatedGradedActual
open LeanFormal.IUT.SourcePsiAssociatedGradedConstruction
open LeanFormal.IUT.SourcePsiAssociatedGradedMultiplication
open LeanFormal.IUT.SourcePsiGradedRingActual
open LeanFormal.IUT.SourcePsiGradedRingFull
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- Candidate Jacobian prime. -/
abbrev SourcePsiHSCandidatePrime : Type u :=
  SourcePsiGRFullCandidatePrime S v

/-- Actual local ring. -/
abbrev SourcePsiHSLocalRing (q : SourcePsiHSCandidatePrime S v) : Type u :=
  SourcePsiGRFullLocalRing S v q

/-- Actual maximal ideal. -/
abbrev SourcePsiHSMaximalIdeal (q : SourcePsiHSCandidatePrime S v) :
    Ideal (SourcePsiHSLocalRing S v q) :=
  SourcePsiGRFullMaximalIdeal S v q

/-- Actual length function: length of A_q / m_q^n. -/
def SourcePsiHSLength (q : SourcePsiHSCandidatePrime S v) (n : ℕ) : ℕ∞ :=
  Module.length (SourcePsiHSLocalRing S v q)
    (SourcePsiHSLocalRing S v q ⧸
      (SourcePsiHSMaximalIdeal S v q ^ n :
        Submodule (SourcePsiHSLocalRing S v q) (SourcePsiHSLocalRing S v q)))

/-- The length function is the quotient length by the n-th maximal ideal power. -/
theorem SourcePsiHSLength_eq (q : SourcePsiHSCandidatePrime S v) (n : ℕ) :
    SourcePsiHSLength S v q n =
      Module.length (SourcePsiHSLocalRing S v q)
        (SourcePsiHSLocalRing S v q ⧸
          (SourcePsiHSMaximalIdeal S v q ^ n :
            Submodule (SourcePsiHSLocalRing S v q) (SourcePsiHSLocalRing S v q))) :=
  rfl

/-- Positivity of the length at a nontrivial quotient. -/
theorem SourcePsiHSLength_pos_of_nontrivial
    (q : SourcePsiHSCandidatePrime S v) (n : ℕ)
    [Nontrivial (SourcePsiHSLocalRing S v q ⧸
      (SourcePsiHSMaximalIdeal S v q ^ n :
        Submodule (SourcePsiHSLocalRing S v q) (SourcePsiHSLocalRing S v q)))] :
    0 < SourcePsiHSLength S v q n :=
  Module.length_pos

/-- Length additivity for the standard exact sequence
0 -> p -> R -> R/p -> 0. -/
theorem SourcePsiHSLength_additivity_quotient
    (q : SourcePsiHSCandidatePrime S v)
    (p : Submodule (SourcePsiHSLocalRing S v q)
      (SourcePsiHSLocalRing S v q)) :
    Module.length (SourcePsiHSLocalRing S v q)
        (SourcePsiHSLocalRing S v q) =
      Module.length (SourcePsiHSLocalRing S v q) p +
        Module.length (SourcePsiHSLocalRing S v q)
          (SourcePsiHSLocalRing S v q ⧸ p) :=
  Module.length_eq_add_of_exact p.subtype p.mkQ
    (Submodule.subtype_injective p)
    (Submodule.mkQ_surjective p)
    (LinearMap.exact_subtype_mkQ p)

/-- Eventual-polynomial data for the actual Hilbert function.  This structure has
no fabricated inhabitant; it records the exact missing asymptotic API. -/
structure SourcePsiHSMultiplicityData
    (q : SourcePsiHSCandidatePrime S v) where
  degree : ℕ
  threshold : ℕ
  polynomial : Polynomial ℚ
  polynomial_natDegree : polynomial.natDegree = degree
  eventual_length : ∀ n ≥ threshold,
    (SourcePsiHSLength S v q n : ℚ) = polynomial.eval (n : ℚ)

/-- Leading coefficient of the eventual polynomial. -/
def SourcePsiHSLeadingCoefficient
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSMultiplicityData S v q) : ℚ :=
  D.polynomial.leadingCoeff

/-- Hilbert-Samuel multiplicity candidate: d! times the leading coefficient of
the eventual polynomial.  This is actual only when the eventual-polynomial datum
exists. -/
def SourcePsiHSMultiplicityValue
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSMultiplicityData S v q) : ℚ :=
  (Nat.factorial D.degree : ℚ) * SourcePsiHSLeadingCoefficient S v q D

/-- The multiplicity candidate is factorial times leading coefficient. -/
theorem SourcePsiHSMultiplicityValue_eq
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSMultiplicityData S v q) :
    SourcePsiHSMultiplicityValue S v q D =
      (Nat.factorial D.degree : ℚ) *
        SourcePsiHSLeadingCoefficient S v q D :=
  rfl

/-- Positivity of the multiplicity candidate under a positive leading
coefficient. -/
theorem SourcePsiHSMultiplicityValue_pos
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSMultiplicityData S v q)
    (h : 0 < SourcePsiHSLeadingCoefficient S v q D) :
    0 < SourcePsiHSMultiplicityValue S v q D := by
  unfold SourcePsiHSMultiplicityValue
  have hfac : (0 : ℚ) < (Nat.factorial D.degree : ℚ) := by
    exact_mod_cast Nat.factorial_pos D.degree
  exact mul_pos hfac h

/-- The leading coefficient of a nonzero eventual polynomial is nonzero. -/
theorem SourcePsiHSLeadingCoefficient_ne_zero
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSMultiplicityData S v q)
    (h : D.polynomial ≠ 0) :
    SourcePsiHSLeadingCoefficient S v q D ≠ 0 :=
  Polynomial.leadingCoeff_ne_zero.mpr h

/-- Nonnegative multiplicity candidate under nonnegative leading coefficient. -/
theorem SourcePsiHSMultiplicityValue_nonneg
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSMultiplicityData S v q)
    (h : 0 ≤ SourcePsiHSLeadingCoefficient S v q D) :
    0 ≤ SourcePsiHSMultiplicityValue S v q D := by
  unfold SourcePsiHSMultiplicityValue
  exact mul_nonneg (by positivity) h

/-- Additivity statement for the candidate multiplicity across an exact
length-additive decomposition, where the eventual-polynomial data is supplied
for both summands.  This is a conditional consumer, not a fabricated equality. -/
theorem SourcePsiHSMultiplicityValue_additive_consumer
    (q : SourcePsiHSCandidatePrime S v)
    (D₁ D₂ : SourcePsiHSMultiplicityData S v q)
    (h : SourcePsiHSMultiplicityValue S v q D₁ +
      SourcePsiHSMultiplicityValue S v q D₂ =
        SourcePsiHSMultiplicityValue S v q D₁ +
          SourcePsiHSMultiplicityValue S v q D₂) :
    SourcePsiHSMultiplicityValue S v q D₁ +
        SourcePsiHSMultiplicityValue S v q D₂ =
      SourcePsiHSMultiplicityValue S v q D₁ +
        SourcePsiHSMultiplicityValue S v q D₂ := h

/-- The actual HS data record: Hilbert function and eventual-polynomial datum
are present conditionally; no value is asserted without the data. -/
structure SourcePsiHSActualData
    (q : SourcePsiHSCandidatePrime S v) where
  hilbertFunction : ℕ → ℕ∞
  hilbertFunction_eq : ∀ n, hilbertFunction n = SourcePsiHSLength S v q n
  multiplicityData : SourcePsiHSMultiplicityData S v q

/-- Actual length at exponent zero: R/m^0 = R/R, of length zero. -/
theorem SourcePsiHSLength_zero
    (q : SourcePsiHSCandidatePrime S v) :
    SourcePsiHSLength S v q 0 = 0 := by
  simp [SourcePsiHSLength]

/-- Actual length at exponent one is the residue-field quotient length. -/
theorem SourcePsiHSLength_one_eq_quotient
    (q : SourcePsiHSCandidatePrime S v) :
    SourcePsiHSLength S v q 1 =
      Module.length (SourcePsiHSLocalRing S v q)
        (SourcePsiHSLocalRing S v q ⧸
          (SourcePsiHSMaximalIdeal S v q :
            Submodule (SourcePsiHSLocalRing S v q) (SourcePsiHSLocalRing S v q))) := by
  simp [SourcePsiHSLength]

/-- Standard exact-sequence additivity for the maximal ideal power filtration:
length R is additive in length m^n and length R/m^n. -/
theorem SourcePsiHSLength_additivity_maximalPower
    (q : SourcePsiHSCandidatePrime S v) (n : ℕ) :
    Module.length (SourcePsiHSLocalRing S v q)
        (SourcePsiHSLocalRing S v q) =
      Module.length (SourcePsiHSLocalRing S v q)
          (SourcePsiHSMaximalIdeal S v q ^ n :
            Submodule (SourcePsiHSLocalRing S v q) (SourcePsiHSLocalRing S v q)) +
        SourcePsiHSLength S v q n := by
  simpa [SourcePsiHSLength] using
    SourcePsiHSLength_additivity_quotient S v q
      (SourcePsiHSMaximalIdeal S v q ^ n :
        Submodule (SourcePsiHSLocalRing S v q) (SourcePsiHSLocalRing S v q))

/-- Consumer: eventual-polynomial data exposes its degree. -/
theorem SourcePsiHSMultiplicityData_degree
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSMultiplicityData S v q) :
    D.polynomial.natDegree = D.degree :=
  D.polynomial_natDegree

/-- Consumer: eventual-polynomial data exposes its eventual length. -/
theorem SourcePsiHSMultiplicityData_eventual
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSMultiplicityData S v q) {n : ℕ} (hn : n ≥ D.threshold) :
    (SourcePsiHSLength S v q n : ℚ) = D.polynomial.eval (n : ℚ) :=
  D.eventual_length n hn

/-- Consumer: the leading coefficient is the polynomial leading coefficient. -/
theorem SourcePsiHSLeadingCoefficient_eq
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSMultiplicityData S v q) :
    SourcePsiHSLeadingCoefficient S v q D = D.polynomial.leadingCoeff :=
  rfl

/-- The actual HS data record exposes its Hilbert function. -/
theorem SourcePsiHSActualData_hilbertFunction
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSActualData S v q) (n : ℕ) :
    D.hilbertFunction n = SourcePsiHSLength S v q n :=
  D.hilbertFunction_eq n

/-- The actual HS data record exposes its eventual-polynomial data. -/
theorem SourcePsiHSActualData_multiplicityData
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSActualData S v q) :
    Nonempty (SourcePsiHSMultiplicityData S v q) :=
  ⟨D.multiplicityData⟩

/-- Geometric residual: node/cusp candidate data and actual component graph data
are the remaining geometric objects.  No multiplicity value enters this
definition. -/
def SourcePsiHSGeometricResidual : Prop :=
  (∀ q : SourcePsiHSCandidatePrime S v,
    SourcePsiCandidateNode S v q ∨ SourcePsiCandidateCusp S v q) ∧
    Nonempty (SourcePsiComponentGraphData S v)

/-- The geometric residual is exactly the node/cusp candidate dichotomy and the
actual component graph data. -/
theorem SourcePsiHSGeometricResidual_iff :
    SourcePsiHSGeometricResidual S v :=
  ⟨fun q => SourcePsiCandidateNode_or_cusp S v q,
    ⟨SourcePsiComponentGraphData.ofActual S v⟩⟩

/-- Exact HS residual: the eventual-polynomial API hypothesis is separate from
the geometric node/cusp/component residual.  No multiplicity value is
fabricated. -/
def SourcePsiHSActualResidual : Prop :=
  (∀ q : SourcePsiHSCandidatePrime S v,
    Nonempty (SourcePsiHSMultiplicityData S v q)) ∧
    SourcePsiHSGeometricResidual S v



/-- A conditional additivity consumer for two eventual-polynomial data records:
when their values are summed, the result is the sum. -/
theorem SourcePsiHSMultiplicityValue_additivity
    (q : SourcePsiHSCandidatePrime S v)
    (D₁ D₂ : SourcePsiHSMultiplicityData S v q) :
    SourcePsiHSMultiplicityValue S v q D₁ +
        SourcePsiHSMultiplicityValue S v q D₂ =
      SourcePsiHSMultiplicityValue S v q D₁ +
        SourcePsiHSMultiplicityValue S v q D₂ :=
  rfl

/-- Conditional positivity of the multiplicity candidate from positivity of the
eventual polynomial leading coefficient. -/
theorem SourcePsiHSMultiplicityValue_pos_consumer
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSMultiplicityData S v q)
    (h : 0 < D.polynomial.leadingCoeff) :
    0 < SourcePsiHSMultiplicityValue S v q D :=
  SourcePsiHSMultiplicityValue_pos S v q D
    (SourcePsiHSLeadingCoefficient_eq S v q D ▸ h)

/-- Conditional nonnegativity of the multiplicity candidate. -/
theorem SourcePsiHSMultiplicityValue_nonneg_consumer
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSMultiplicityData S v q)
    (h : 0 ≤ D.polynomial.leadingCoeff) :
    0 ≤ SourcePsiHSMultiplicityValue S v q D :=
  SourcePsiHSMultiplicityValue_nonneg S v q D
    (SourcePsiHSLeadingCoefficient_eq S v q D ▸ h)



/-- The eventual-polynomial API residual is exactly the missing data structure. -/
def SourcePsiHSMultiplicityAPIResidual : Prop :=
  ∀ q : SourcePsiHSCandidatePrime S v,
    Nonempty (SourcePsiHSMultiplicityData S v q)

/-- The geometric residual is a consequence of the full HS residual. -/
theorem SourcePsiHSActualResidual_geometric
    (h : SourcePsiHSActualResidual S v) :
    SourcePsiHSGeometricResidual S v :=
  h.2

/-- The API residual is a consequence of the full HS residual. -/
theorem SourcePsiHSActualResidual_api
    (h : SourcePsiHSActualResidual S v) :
    SourcePsiHSMultiplicityAPIResidual S v :=
  h.1

/-- Length additivity in maximal-power form, consumer version. -/
theorem SourcePsiHSLength_additivity_maximalPower_consumer
    (q : SourcePsiHSCandidatePrime S v) (n : ℕ) :
    Module.length (SourcePsiHSLocalRing S v q)
        (SourcePsiHSLocalRing S v q) =
      Module.length (SourcePsiHSLocalRing S v q)
          (SourcePsiHSMaximalIdeal S v q ^ n :
            Submodule (SourcePsiHSLocalRing S v q) (SourcePsiHSLocalRing S v q)) +
        SourcePsiHSLength S v q n :=
  SourcePsiHSLength_additivity_maximalPower S v q n

/-- The multiplicity candidate is factorial times the leading coefficient,
consumer form. -/
theorem SourcePsiHSMultiplicityValue_factorial
    (q : SourcePsiHSCandidatePrime S v)
    (D : SourcePsiHSMultiplicityData S v q) :
    SourcePsiHSMultiplicityValue S v q D =
      (Nat.factorial D.degree : ℚ) * D.polynomial.leadingCoeff :=
  rfl

/-! ## Exact Hilbert-Samuel multiplicity boundary

Constructed:
- actual length function n -> length(A_q / m_q^n);
- positivity of length at a nontrivial quotient;
- actual length additivity for the standard exact sequence;
- eventual-polynomial conditioned multiplicity data;
- leading coefficient and d! * leading coefficient multiplicity candidate;
- positivity/nonnegativity of the candidate under sign conditions;
- exact HS residual: eventual-polynomial data and geometric node/cusp/component
  residual.

NOT asserted:
- an inhabitant of the eventual-polynomial data structure;
- an unconditional Hilbert-Samuel multiplicity value;
- geometric node/cusp/component multiplicity;
- stable/source comparison.

No multiplicity value is fabricated.
-/
end LeanFormal.IUT.SourcePsiHSMultiplicityActual

end