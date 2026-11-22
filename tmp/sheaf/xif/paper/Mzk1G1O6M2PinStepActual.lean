/- O6 P1: the Belyi degree-reduction step for the general branch pinning (route §4.3):
from a finite set of irreducible polynomials of largest degree ≥ 2 obtain a set with
strictly smaller lexicographic measure `(max degree, count at max degree)`.
REUSE (imported, not ported):
- `tmp.external.ported.belyi_poly...TauCeti.exists_irreducible_finset_dvd_comp` (Belyi).
- `Mzk1G1O6M2PinGeneralActual.pinMeasure` / `pinMeasure_lex_of_reduction` (measure, this lane).
- `Polynomial.separable_iff_derivative_ne_zero` / `Irreducible.separable` (Mathlib).
DEDUP: the step itself was not assembled in our tree. -/
import tmp.sheaf.xif.paper.Mzk1G1O6M2PinGeneralActual
import tmp.external.ported.belyi_poly.TauCeti.FieldTheory.Minpoly.BelyiReduction
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinStepActual
open LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinGeneralActual

/-- Over a field of characteristic zero, an irreducible polynomial of degree at least two
has nonzero derivative (it is separable). -/
theorem derivative_ne_zero_of_irreducible {F : Type*} [Field F] [CharZero F] {μ : F[X]}
    (hμ : Irreducible μ) (hdeg : 2 ≤ μ.natDegree) : Polynomial.derivative μ ≠ 0 :=
  (Polynomial.separable_iff_derivative_ne_zero hμ).mp hμ.separable

/-- The one-step reduction property used by the general pinning recursion. -/
def PinReductionStep : Prop :=
  ∀ P : Finset ℚ[X], (∀ p ∈ P, Irreducible p) → 2 ≤ pinMaxDeg P →
    ∃ P' : Finset ℚ[X], (∀ p ∈ P', Irreducible p) ∧
      pinLt P' P

/-- **The Belyi degree-reduction supplies the recursion step** (TauCeti donor). -/
theorem pinReductionStep_holds : PinReductionStep := by
  intro P hP hdeg2
  classical
  have hne : P.Nonempty := by
    rcases Finset.eq_empty_or_nonempty P with rfl | h
    · simp [pinMaxDeg] at hdeg2
    · exact h
  obtain ⟨μ, hμP, hμmax⟩ := Finset.exists_mem_eq_sup P hne Polynomial.natDegree
  have hμirr : Irreducible μ := hP μ hμP
  have hdegμ : 2 ≤ μ.natDegree := by
    have h1 : pinMaxDeg P = μ.natDegree := hμmax
    rwa [h1] at hdeg2
  have hμ' : Polynomial.derivative μ ≠ 0 := derivative_ne_zero_of_irreducible hμirr hdegμ
  have hdegall : ∀ p ∈ P, p.natDegree ≤ μ.natDegree := by
    intro p hp
    exact (pinMaxDeg_le hp).trans (le_of_eq hμmax)
  obtain ⟨P', hP'irr, hP'deg, hcount, -, -⟩ :=
    TauCeti.exists_irreducible_finset_dvd_comp (F := ℚ) hP hμP hμ' hdegall hdegμ
  exact ⟨P', hP'irr, pinLt_of_reduction hμP hdegall hP'deg hcount⟩

#print axioms derivative_ne_zero_of_irreducible
#print axioms pinReductionStep_holds
end LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinStepActual