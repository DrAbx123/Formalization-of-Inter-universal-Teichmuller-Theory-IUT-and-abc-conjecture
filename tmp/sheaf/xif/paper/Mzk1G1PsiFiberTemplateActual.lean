import tmp.sheaf.xif.paper.Mzk1G1PsiFiberFiniteActual
import Mathlib.Tactic

/-!
# Fibre finiteness templates for A-4 (chart-coordinate independent)

These two templates are independent of the chart conventions of hPoly / hPolyL: once the
chart coordinate u of a piece is known, the fibre of the point q on that piece is
{p : PrimeSpectrum R | u - algebraMap Q R q in p.asIdeal}, whose finiteness follows from the
finiteness over Q of the quotient R / (u - q).  Consumer: B1 / Mzk1G1PhiFiberFiniteFixedActual.
-/

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiFiberTemplateActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFiberFiniteActual

/-- Chart-coordinate fibre template: for a finitely generated Q-algebra quotient, the points
where the coordinate u equals the rational value q are finite. -/
theorem finite_primes_of_coord {R : Type} [CommRing R] [Algebra ℚ R] (u : R) (q : ℚ)
    (hfin : Module.Finite ℚ (R ⧸ Ideal.span ({u - algebraMap ℚ R q} : Set R))) :
    {p : PrimeSpectrum R | (u - algebraMap ℚ R q) ∈ p.asIdeal}.Finite :=
  finite_primes_of_finite_quotient (u - algebraMap ℚ R q) hfin

/- Reduction of the polynomial-coordinate case to the chart-coordinate template: if the
coordinate is a polynomial f in a generator u with f - q factored as (u - q) up to a nonzero
factor, the same template applies.  The polynomial tower bookkeeping (Q[t] -> Q[t]/(f) ->
R/(f(u)) with Module.Finite.trans and of_restrictScalars_finite) is recorded in
Mzk1G1PsiQuotientFiniteActual (see its quot_finiteDim_map recipe) and is deliberately not
restated here. -/

#print axioms finite_primes_of_coord
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiFiberTemplateActual
