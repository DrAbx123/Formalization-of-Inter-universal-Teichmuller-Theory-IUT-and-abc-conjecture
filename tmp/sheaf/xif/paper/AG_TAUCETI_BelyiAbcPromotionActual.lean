import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.Belyi
import tmp.external.ported.tauceti_belyi_core.TauCeti.NumberTheory.AbcConjecture

/-!
# AG-TAUCETI Belyi/abc promotion layer (first-class importable; audit component)

COMPONENT, not a paper object.  Named consumers: mainline AbcStatementAlignment,
abc (Mzk1 Belyification consumer), hull GenEll15 GeometricCore, Lead AG-INFRA-PLAN.

Ported assets (Apache-2.0 attribution in ported headers; canonical root
tmp/external/ported/tauceti_belyi_core; all checker-CITABLE with probes trio):
* CriticalValues/Belyi: critical-value machinery, Belyi polynomial B_{m,n},
  critical points containment and polynomial Belyification (rational/algebraic);
* AbcConjecture: standard Masser-Oesterle statement + integer forms.
This layer re-exports the declarations consumed by our streams with explicit
types (no axiom/fake data; complete ported proofs).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.AG_TAUCETI_BelyiAbcPromotionActual

open Polynomial TauCeti UniqueFactorizationMonoid

/-- The Belyi polynomial B_{m,n} over a field K. -/
noncomputable def promotion_belyiPolynomial (K : Type*) [Field K] (m n : ℕ) : K[X] :=
  TauCeti.belyiPolynomial K m n

/-- COMPLETE PROOF (ported): the critical points of B_{m,n} lie in
{0, 1, m/(m+n)} in every field extension of K. -/
theorem promotion_rootSet_derivative_belyiPolynomial_subset
    (K : Type*) [Field K] [CharZero K] (L : Type*) [Field L] [Algebra K L] (m n : ℕ) :
    (derivative (TauCeti.belyiPolynomial K m n)).rootSet L ⊆ {0, 1, (m : L) / (m + n)} :=
  TauCeti.rootSet_derivative_belyiPolynomial_subset (K := K) L m n

/-- Statement row: the abc conjecture (Masser-Oesterle). -/
def promotion_AbcConjecture : Prop := TauCeti.AbcConjecture

/-- COMPLETE PROOF (ported): integer form of the abc conjecture. -/
theorem promotion_abcConjecture_iff_nat :
    promotion_AbcConjecture ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b c : ℕ, 0 < a → 0 < b → a.Coprime b → a + b = c →
        (c : ℝ) ≤ C * ((radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε) :=
  TauCeti.abcConjecture_iff_nat

end LeanFormal.IUT.XiFPaper.AG_TAUCETI_BelyiAbcPromotionActual
