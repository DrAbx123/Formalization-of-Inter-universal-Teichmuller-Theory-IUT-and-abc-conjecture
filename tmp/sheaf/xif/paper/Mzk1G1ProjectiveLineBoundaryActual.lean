import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineGluedActual
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual

/-- The closed point of the affine chart Q[s] where the coordinate s equals r, as the set
of primes containing X - r. -/
noncomputable def chartPoint (r : ℚ) : Set (PrimeSpectrum (Polynomial ℚ)) :=
  {p | Polynomial.X - Polynomial.C r ∈ p.asIdeal}

/-- The point 0 of P^1: the origin lambda = 0 of the lambda-chart (the affine coordinate
of P^1 that is used for the Belyi values). -/
noncomputable def p1Zero : Set projectiveLineGlued :=
  localChart0.base '' chartPoint 0

/-- The point 1 of P^1: the point lambda = 1 of the lambda-chart. -/
noncomputable def p1One : Set projectiveLineGlued :=
  localChart0.base '' chartPoint 1

/-- The point infinity of P^1: the point at infinity of the lambda-chart, i.e. t = 0 in
the t-chart (transition t = lambda^{-1}). -/
noncomputable def p1Infinity : Set projectiveLineGlued :=
  localChartInf.base '' chartPoint 0

/-- THE BOUNDARY VALUE SET {0, 1, infinity} of P^1 in the glued chart model. -/
noncomputable def boundarySetGlued : Set projectiveLineGlued :=
  p1Zero ∪ p1One ∪ p1Infinity

/-- The boundary of a scheme morphism phi : X -> P^1, as a point set: the preimage of
{0, 1, infinity}. -/
noncomputable def boundaryPreimageGlued {X : Scheme} (phi : X ⟶ projectiveLineGlued) :
    Set X := phi.base ⁻¹' boundarySetGlued

/-- The polynomial X - r is irreducible. -/
theorem irreducible_X_sub_C (r : ℚ) : Irreducible (Polynomial.X - Polynomial.C r : Polynomial ℚ) :=
  Polynomial.irreducible_X_sub_C r

/-- The ideal (X - r) is prime in Q[X]. -/
theorem isPrime_span_X_sub_C (r : ℚ) :
    (Ideal.span ({Polynomial.X - Polynomial.C r} : Set (Polynomial ℚ))).IsPrime := by
  rw [Ideal.span_singleton_prime]
  · exact (irreducible_X_sub_C r).prime
  · exact (Polynomial.monic_X_sub_C r).ne_zero

/-- The chart point V(X - r) is nonempty. -/
theorem chartPoint_nonempty (r : ℚ) : (chartPoint r).Nonempty :=
  ⟨⟨Ideal.span ({Polynomial.X - Polynomial.C r} : Set (Polynomial ℚ)), isPrime_span_X_sub_C r⟩,
    Ideal.subset_span (Set.mem_singleton _)⟩

/-- The three boundary points are nonempty subsets of P^1. -/
theorem p1Zero_nonempty : (p1Zero).Nonempty :=
  (chartPoint_nonempty 0).image localChart0.base

theorem p1One_nonempty : (p1One).Nonempty :=
  (chartPoint_nonempty 1).image localChart0.base

theorem p1Infinity_nonempty : (p1Infinity).Nonempty :=
  (chartPoint_nonempty 0).image localChartInf.base

#print axioms chartPoint_nonempty
#print axioms p1Zero_nonempty
#print axioms p1One_nonempty
#print axioms boundarySetGlued
#print axioms boundaryPreimageGlued
end LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
