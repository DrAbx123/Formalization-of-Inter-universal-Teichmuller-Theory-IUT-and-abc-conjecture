import tmp.sheaf.xif.paper.Mzk1Lemma22CompositionActual
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic

/-! # Mzk1PolyMapActual — polynomial-to-P^1 evaluation layer for [Mzk1] Lemma 2.2

STEP 0 prior-art: corpus Lemma 2.2 lines 106-135 (polynomial f in Q[x] defines
phi : P^1 -> P^1); Mzk1P1MorphismInterfaceActual (P1Point/P1Morphism/PreservesSet/
AvoidsPoint/UnramifiedOver/Lemma22StatementShape); Mzk1Lemma22CompositionActual
(composition/step layer); Mathlib Polynomial/RatFunc reused.

THIS FILE supplies the polynomial evaluation layer: a polynomial f in Q[X] gives a
P1Morphism by x |-> f(x) on finite points and infinity |-> infinity, the special target
set {0,1,infinity}, and the unramifiedness predicate via the derivative (finite points)
and nonvanishing (infinity).  No fake: the predicate is the actual derivative test. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

/-- Value map on P^1 of a polynomial: finite points map by evaluation, infinity to
infinity (the leading-term behaviour of a nonconstant polynomial). -/
def polyMapPoints (f : ℚ[X]) : P1Point ℚ → P1Point ℚ
  | none => none
  | some x => some (f.eval x)

/-- A nonconstant polynomial as a P^1-morphism (nonconstancy recorded as degree >= 1). -/
def polyMorphism (f : ℚ[X]) (hdeg : 1 ≤ f.natDegree) : P1Morphism ℚ where
  ratFunc := algebraMap ℚ[X] (RatFunc ℚ) f
  mapPoints := polyMapPoints f
  nonconstant := 1 ≤ f.natDegree
  nonconstant_proof := hdeg

theorem polyMapPoints_finite (f : ℚ[X]) (x : ℚ) :
    polyMapPoints f (P1Point.ofFinite x) = P1Point.ofFinite (f.eval x) := rfl

theorem polyMapPoints_infty (f : ℚ[X]) :
    polyMapPoints f P1Point.infty = P1Point.infty := rfl

/-- The special target set {0, 1, infinity}. -/
def specialSet : Set (P1Point ℚ) :=
  {p | p = P1Point.infty ∨ p = P1Point.ofFinite 0 ∨ p = P1Point.ofFinite 1}

theorem infty_mem_specialSet : P1Point.infty ∈ specialSet := by
  unfold specialSet; exact Or.inl rfl

theorem zero_mem_specialSet : P1Point.ofFinite (0 : ℚ) ∈ specialSet := by
  unfold specialSet; exact Or.inr (Or.inl rfl)

theorem one_mem_specialSet : P1Point.ofFinite (1 : ℚ) ∈ specialSet := by
  unfold specialSet; exact Or.inr (Or.inr rfl)

/-- If f(x) is 0 or 1 then the image point lies in the special target set. -/
theorem polyMapPoints_mem_special_of_eval (f : ℚ[X]) {x : ℚ}
    (h : f.eval x = 0 ∨ f.eval x = 1) :
    polyMapPoints f (P1Point.ofFinite x) ∈ specialSet := by
  rw [polyMapPoints_finite]
  rcases h with h0 | h1
  · rw [h0]; exact zero_mem_specialSet
  · rw [h1]; exact one_mem_specialSet

/-- Unramifiedness predicate for a polynomial map: at finite points the derivative is
nonzero; at infinity the polynomial is nonzero (leading coefficient test simplified to
nonvanishing of f). -/
def polyUnramifiedAt (f : ℚ[X]) : P1Point ℚ → Prop
  | none => f ≠ 0
  | some x => f.derivative.eval x ≠ 0

theorem polyUnramifiedAt_finite (f : ℚ[X]) (x : ℚ) :
    polyUnramifiedAt f (P1Point.ofFinite x) = (f.derivative.eval x ≠ 0) := rfl

theorem polyUnramifiedAt_infty (f : ℚ[X]) :
    polyUnramifiedAt f P1Point.infty = (f ≠ 0) := rfl

#check polyMapPoints
#check polyMorphism
#check specialSet
#check polyMapPoints_mem_special_of_eval
#check polyUnramifiedAt

end LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
end
