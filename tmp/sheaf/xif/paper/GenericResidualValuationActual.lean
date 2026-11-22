import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# Generic residual valuation

No Valued.v instance is used here.  For an explicit valuation

  v : Valuation L (WithZero (Multiplicative Int))

and q, pi : L with

  v q = exp (-exponent),   v pi = exp (-1),

we prove v (q / pi^n) = 1 whenever (n : Int) = exponent.

The second part records the coherence condition needed to instantiate this at a
Completion place, without rewriting across different Valued.v instances.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.GenericResidualValuationActual

universe u

variable {L : Type u} [Field L]

/-- Power valuation of an exp(-1)-uniformizer. -/
theorem uniformizer_pow_valuation
    (v : Valuation L (WithZero (Multiplicative Int)))
    (pi : L) (hpi : v pi = WithZero.exp (-1)) (n : Nat) :
    v (pi ^ n) = WithZero.exp (-(n : Int)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Valuation.map_mul, ih, hpi, ← WithZero.exp_add]
      congr 1
      push_cast
      ring

/-- Generic residual valuation: q / pi^n has valuation one. -/
theorem residual_valuation
    (v : Valuation L (WithZero (Multiplicative Int)))
    (q pi : L) (n : Nat) (exponent : Int)
    (hq : v q = WithZero.exp (-exponent))
    (hpi : v pi = WithZero.exp (-1))
    (hn : (n : Int) = exponent) :
    v (q / pi ^ n) = 1 := by
  rw [Valuation.map_div, hq, uniformizer_pow_valuation v pi hpi n, ← hn]
  exact div_self WithZero.exp_ne_zero

/-- Coherence input needed to instantiate at a completion place.  The equality
to Valued.v is a proposition field, not an assumed theorem. -/
structure CoherentCompletionPlaceValuation
    (L : Type u) [Field L] where
  v : Valuation L (WithZero (Multiplicative Int))
  valued_v_eq : Prop
  valuation_instances_coherent : Prop

/-- Instantiation wrapper: the generic residual valuation is proved for the
explicit coherent valuation, without rewriting across instances. -/
theorem residual_valuation_of_coherent
    (C : CoherentCompletionPlaceValuation L)
    (q pi : L) (n : Nat) (exponent : Int)
    (hq : C.v q = WithZero.exp (-exponent))
    (hpi : C.v pi = WithZero.exp (-1))
    (hn : (n : Int) = exponent) :
    C.v (q / pi ^ n) = 1 :=
  residual_valuation C.v q pi n exponent hq hpi hn

end LeanFormal.IUT.XiFPaper.GenericResidualValuationActual
end
