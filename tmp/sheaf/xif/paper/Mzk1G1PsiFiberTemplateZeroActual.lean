import tmp.sheaf.xif.paper.Mzk1G1PsiFiberTemplateActual
import Mathlib.Tactic

/-!
# Fibre template at the value 0 (padding for A-4 / c2 chart reductions)

Specialisation of Mzk1G1PsiFiberTemplateActual.finite_primes_of_coord to q = 0, which is the
form used for the boundary point p1Zero (= lambda = 0) in the phiFixedL fibre calculations.
-/

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiFiberTemplateZeroActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFiberTemplateActual

/-- Points where a chart coordinate vanishes are finite, given finiteness of the quotient. -/
theorem finite_primes_of_coord_zero {R : Type} [CommRing R] [Algebra ℚ R] (u : R)
    (hfin : Module.Finite ℚ (R ⧸ Ideal.span ({u} : Set R))) :
    {p : PrimeSpectrum R | u ∈ p.asIdeal}.Finite := by
  have h := finite_primes_of_coord (R := R) u 0 (by simpa using hfin)
  simpa using h

#print axioms finite_primes_of_coord_zero
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiFiberTemplateZeroActual
