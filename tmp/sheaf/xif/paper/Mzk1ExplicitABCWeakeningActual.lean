import LeanFormal.IUT.ABCBridge.Statement
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCCards

/-! Mainline (A488 explicit-first): the explicit/effective ABC form and its weakening
  to the qualitative `ABCConjecture`.  The shape follows the explicit-constant form of
  `Cor312ToABCCards.explicitEstimatesThm54Shape` (closed constant `C(epsilon)`), but in
  the repository radical form: a single explicit function `K : Real -> Real` giving the
  constant for every epsilon, with no existential hiding inside the quantifier order.

  Main theorem: `ExplicitABC => ABCConjecture` (drop the explicit constants / use
  `Classical.choice` to extract `K`), which is the closing lemma of the explicit route. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ExplicitABCWeakeningActual

noncomputable section

open LeanFormal.IUT

/-- Explicit ABC: a single explicit constant function `K(epsilon)` bounds every ABC
  triple.  This is the explicit-constant form; the function itself is data, so the
  statement is computable in shape (no existential on the constant inside `forall`). -/
def ExplicitABC : Prop :=
  ∃ K : Real → Real, ∀ epsilon : Real, 0 < epsilon →
    ∀ a b c : Nat, IsABCTriple a b c →
      (c : Real) ≤ K epsilon * Real.rpow (radical (a * b * c) : Real) (1 + epsilon)

/-- Closed-form explicit ABC: the constant function is given by a concrete closed form
  `C`, mirroring `explicitEstimatesThm54ExpConstant` in `Cor312ToABCCards`. -/
def ClosedFormExplicitABC (C : Real → Real) : Prop :=
  ∀ epsilon : Real, 0 < epsilon →
    ∀ a b c : Nat, IsABCTriple a b c →
      (c : Real) ≤ C epsilon * Real.rpow (radical (a * b * c) : Real) (1 + epsilon)

/-- The explicit form is exactly the per-epsilon `ABCInequality` statement with a
  uniform constant function (definitional unfolding). -/
theorem explicitABC_iff_forall_ABCInequality :
    ExplicitABC ↔
      ∃ K : Real → Real, ∀ epsilon : Real, 0 < epsilon →
        ∀ a b c : Nat, IsABCTriple a b c →
          ABCInequality epsilon (K epsilon) a b c :=
  Iff.rfl

/-- A closed-form constant family gives the explicit ABC form. -/
theorem explicitABC_of_closedForm (C : Real → Real) (h : ClosedFormExplicitABC C) :
    ExplicitABC :=
  ⟨C, h⟩

/-- **Explicit ABC implies ABCConjecture** (the explicit route closing lemma): drop the
  explicit constants by taking `K(epsilon) = max (K epsilon) 1 > 0`; the bound is
  unchanged after replacing the multiplicative constant by its positive maximum. -/
theorem abcConjecture_of_explicitABC (h : ExplicitABC) : ABCConjecture := by
  obtain ⟨K, hK⟩ := h
  intro epsilon hepsilon
  refine ⟨max (K epsilon) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro a b c habc
  have hc := hK epsilon hepsilon a b c habc
  have hr : (0 : Real) ≤ Real.rpow (radical (a * b * c) : Real) (1 + epsilon) := by
    exact Real.rpow_nonneg (by exact_mod_cast Nat.zero_le _) _
  have hle : K epsilon * Real.rpow (radical (a * b * c) : Real) (1 + epsilon) ≤
      max (K epsilon) 1 * Real.rpow (radical (a * b * c) : Real) (1 + epsilon) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hr
  exact le_trans hc hle

/-- The closed-form explicit route closes to `ABCConjecture` (constant extraction via
  `Classical.choice` when only a family is supplied). -/
theorem abcConjecture_of_closedForm (C : Real → Real)
    (h : ClosedFormExplicitABC C) : ABCConjecture :=
  abcConjecture_of_explicitABC (explicitABC_of_closedForm C h)

end

end LeanFormal.IUT.XiFPaper.Mzk1ExplicitABCWeakeningActual