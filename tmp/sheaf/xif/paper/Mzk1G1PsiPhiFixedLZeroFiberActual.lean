import tmp.sheaf.xif.paper.Mzk1G1PsiFiberTemplateActual
import Mathlib.Tactic

/-! Fibre template at the value zero (A-4 / p1Zero reductions). Consumer: B1. -/

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiPhiFixedLZeroFiberActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFiberTemplateActual

/-- If the quotient by (u) is finite over Q, the primes containing u are finite. -/
theorem finite_primes_of_coord_zero {R : Type} [CommRing R] [Algebra ℚ R] (u : R)
    (hfin : Module.Finite ℚ (R ⧸ Ideal.span ({u} : Set R))) :
    {p : PrimeSpectrum R | u ∈ p.asIdeal}.Finite := by
  have hI : Ideal.span ({u - algebraMap ℚ R (0 : ℚ)} : Set R) = Ideal.span ({u} : Set R) := by
    simp
  have h := finite_primes_of_coord (R := R) u 0 (by rw [hI]; exact hfin)
  simpa using h

#print axioms finite_primes_of_coord_zero
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiPhiFixedLZeroFiberActual
