import Mathlib.RingTheory.Artinian.Module
import Mathlib.Tactic

/-!
# Finite spectra of Artinian rings (adapter for B1 6(iii), route-approved line)

For the fibre finiteness of phi = hPoly . psi we use: R n is finite over Q[X] (y is integral:
y^n = 1 - X^n), so for a nonzero polynomial f the quotient  R n / (f)  is finite dimensional
over Q, hence Artinian, hence has finitely many prime ideals.  The fibres of the chart
polynomial map are then Spec of such quotients.

This file records the reusable adapter: an Artinian commutative ring has finitely many primes.
Mathlib ingredients: instance Finite (MaximalSpectrum R)
(RingTheory/Artinian/Module.lean:523) and primeSpectrumEquivMaximalSpectrum (:560).
-/

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiArtinianSpectrumActual

/-- An Artinian commutative ring has only finitely many prime ideals. -/
theorem finite_primeSpectrum_of_isArtinian (R : Type) [CommRing R] [IsArtinianRing R] :
    Finite (PrimeSpectrum R) :=
  Finite.of_equiv _ (IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := R)).symm

/-- Consequently the prime spectrum of an Artinian ring is a finite set. -/
theorem finite_set_primeSpectrum_of_isArtinian (R : Type) [CommRing R] [IsArtinianRing R] :
    (Set.univ : Set (PrimeSpectrum R)).Finite :=
  Set.finite_univ

/-- Finite dimensionality over a field makes a commutative algebra Artinian
(FiniteDimensional => IsArtinianRing, via IsArtinianRing.of_finite). -/
theorem isArtinianRing_of_moduleFinite (A : Type) [CommRing A] [Algebra ℚ A]
    [Module.Finite ℚ A] : IsArtinianRing A :=
  IsArtinianRing.of_finite ℚ A

#print axioms finite_primeSpectrum_of_isArtinian
#print axioms finite_set_primeSpectrum_of_isArtinian
#print axioms isArtinianRing_of_moduleFinite
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiArtinianSpectrumActual
