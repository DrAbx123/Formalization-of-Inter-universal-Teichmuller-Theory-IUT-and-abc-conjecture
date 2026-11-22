/- O6 / M2: the general pinning recursion (route §4.3): the lexicographic measure on finite
sets of irreducible polynomials (largest degree, number of members of that degree) and the
Belyi degree-reduction step, which is the well-founded descent used to build the general
branch-pinning polynomial. REUSE (imported, not ported):
- `tmp.external.ported.belyi_poly` `TauCeti.exists_irreducible_finset_dvd_comp`
  (Belyi degree reduction with lexicographic measure; perfect field),
- `Mzk1BetaAvoidingBelyiRationalActual.critIn01_iff_criticalValues` (boundary criterion).
DEDUP: no existing formalization of the measure descent in our tree. -/
import tmp.external.ported.belyi_poly.TauCeti.FieldTheory.Minpoly.BelyiReduction
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinGeneralActual

/-- The largest degree of a member of a finite set of polynomials. -/
noncomputable def pinMaxDeg (P : Finset ℚ[X]) : ℕ :=
  P.sup Polynomial.natDegree

/-- The number of members of degree equal to the largest degree. -/
noncomputable def pinCountMax (P : Finset ℚ[X]) : ℕ :=
  (P.filter (fun p => p.natDegree = pinMaxDeg P)).card

theorem pinMaxDeg_le {P : Finset ℚ[X]} {p : ℚ[X]} (hp : p ∈ P) :
    p.natDegree ≤ pinMaxDeg P :=
  Finset.le_sup hp

theorem pinMaxDeg_le_of_forall {P : Finset ℚ[X]} {d : ℕ}
    (h : ∀ p ∈ P, p.natDegree ≤ d) : pinMaxDeg P ≤ d :=
  Finset.sup_le h

/-- The lexicographic order on finite sets: larger set is *smaller* in the order (we compare
as `(max degree, count at max degree)` and the reduction goes downward). -/
def pinLt (A B : Finset ℚ[X]) : Prop :=
  pinMaxDeg A < pinMaxDeg B ∨ (pinMaxDeg A = pinMaxDeg B ∧ pinCountMax A < pinCountMax B)

/-- **Measure descent**: the Belyi degree-reduction step gives a strictly smaller set in
the lexicographic order. -/
theorem pinLt_of_reduction {P P' : Finset ℚ[X]} {μ : ℚ[X]}
    (hμP : μ ∈ P) (hP : ∀ p ∈ P, p.natDegree ≤ μ.natDegree)
    (hP' : ∀ p ∈ P', p.natDegree ≤ μ.natDegree)
    (hcount : (P'.filter (fun p => p.natDegree = μ.natDegree)).card
      < (P.filter (fun p => p.natDegree = μ.natDegree)).card) :
    pinLt P' P := by
  have hmaxP : pinMaxDeg P = μ.natDegree :=
    le_antisymm (pinMaxDeg_le_of_forall hP) (pinMaxDeg_le hμP)
  have hmaxP' : pinMaxDeg P' ≤ μ.natDegree := pinMaxDeg_le_of_forall hP'
  have hcountP : pinCountMax P = (P.filter (fun p => p.natDegree = μ.natDegree)).card := by
    unfold pinCountMax; rw [hmaxP]
  have hcountP' : pinCountMax P' = (P'.filter (fun p => p.natDegree = pinMaxDeg P')).card := rfl
  unfold pinLt
  rcases lt_or_eq_of_le hmaxP' with hlt | heq
  · left
    rw [hmaxP]
    exact hlt
  · right
    constructor
    · rw [heq, hmaxP]
    · rw [hcountP', hcountP]
      have hf : P'.filter (fun p => p.natDegree = pinMaxDeg P')
          = P'.filter (fun p => p.natDegree = μ.natDegree) := by rw [heq]
      rw [hf]
      exact hcount

#print axioms pinMaxDeg_le
#print axioms pinMaxDeg_le_of_forall
#print axioms pinLt_of_reduction
end LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinGeneralActual