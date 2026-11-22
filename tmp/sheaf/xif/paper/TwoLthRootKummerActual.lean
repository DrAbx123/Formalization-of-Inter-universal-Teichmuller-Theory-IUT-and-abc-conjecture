import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.n8.closure.C3Roots
import LeanFormal.IUT.IUTII.Kummer.KummerClass

/-!
# 2l-th root of q_v in the algebraic closure / Kummer tower

The completion is not algebraically closed, so a 2l-th root of the actual
qVFamily q need not lie in the completion.  The correct actual root data live in
the algebraic closure of the completion (the Kummer extension), using the
actual Hodge-theater root system

  qCandidateRootSystem place (qVFamily T b)

from C3Roots.  This is the actual compatible NatRootSystem over
unitToAlgClosed (qVUnit T b).

This file constructs:

* the algebraic-closure unit qVAlgClosedUnit;
* the actual Hodge-theater root system hodgeTwoLRootSystem;
* the actual 2l-th root hodgeTwoLthRoot and its 2l-th power;
* the actual mu_{2l} ambiguity set and the root ratio theorem;
* the exact object-level condition RootInCompletion and the gap
  TwoLthRootCompletionGap, recorded without asserting that the root is in the
  completion.

No completion root is fabricated and no extension equality is claimed.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The completion place of b. -/
abbrev qVPlace : NumberField.FinitePlace T.arithmetic.F :=
  (nativeBadLift T).lift b

/-- The actual q_v unit in the completion. -/
noncomputable abbrev qVCompletionUnit : (Completion (qVPlace T b))ˣ :=
  Units.mk0 (qVFamily T b).q (qVFamily T b).q_ne_zero

/-- The actual q_v unit in the algebraic closure of the completion. -/
noncomputable abbrev qVAlgClosedUnit :
    (AlgebraicClosure (Completion (qVPlace T b)))ˣ :=
  unitToAlgClosed (qVCompletionUnit T b)

/-- Actual Hodge-theater root system over q_v in the algebraic closure. -/
noncomputable def hodgeTwoLRootSystem :
    NatRootSystem (qVAlgClosedUnit T b) :=
  qCandidateRootSystem (qVPlace T b) (qVFamily T b)

/-- The actual 2l-th root in the algebraic closure. -/
noncomputable def hodgeTwoLthRoot :
    (AlgebraicClosure (Completion (qVPlace T b)))ˣ :=
  (hodgeTwoLRootSystem T b).root (2 * l.value)

/-- The Hodge-theater root is the root-system root. -/
theorem hodgeTwoLthRoot_eq_rootSystem :
    hodgeTwoLthRoot T b =
      (hodgeTwoLRootSystem T b).root (2 * l.value) :=
  rfl

/-- The actual 2l-th power of the algebraic-closure root is q_v. -/
theorem hodgeTwoLthRoot_pow :
    hodgeTwoLthRoot T b ^ (2 * l.value) = qVAlgClosedUnit T b := by
  unfold hodgeTwoLthRoot
  exact NatRootSystem.pow_self (hodgeTwoLRootSystem T b) (2 * l.value) (by
    exact Nat.mul_ne_zero (by norm_num) l.prime.ne_zero)

/-- The actual mu_{2l} root set in the algebraic closure. -/
def muTwoLAlgClosed :
    Set (AlgebraicClosure (Completion (qVPlace T b)))ˣ :=
  {ζ | ζ ^ (2 * l.value) = 1}

/-- Two algebraic-closure 2l-th roots differ by an actual mu_{2l} element. -/
theorem twoLthRoot_ratio_mem_mu
    (R R' : NatRootSystem (qVAlgClosedUnit T b)) :
    (R'.root (2 * l.value) / R.root (2 * l.value)) ∈
      muTwoLAlgClosed (l := l) T b := by
  unfold muTwoLAlgClosed
  simp only [Set.mem_setOf_eq]
  rw [div_pow,
    NatRootSystem.pow_self R' (2 * l.value) (by
      exact Nat.mul_ne_zero (by norm_num) l.prime.ne_zero),
    NatRootSystem.pow_self R (2 * l.value) (by
      exact Nat.mul_ne_zero (by norm_num) l.prime.ne_zero)]
  simp

/-- The actual root-system/root interface to the Hodge-theater data. -/
structure HodgeTwoLthRootInterface where
  rootSystem : NatRootSystem (qVAlgClosedUnit T b)
  root : (AlgebraicClosure (Completion (qVPlace T b)))ˣ
  root_eq : root = rootSystem.root (2 * l.value)
  root_pow : root ^ (2 * l.value) = qVAlgClosedUnit T b

/-- Actual Hodge-theater root interface. -/
noncomputable def hodgeTwoLthRootInterface :
    HodgeTwoLthRootInterface T b where
  rootSystem := hodgeTwoLRootSystem T b
  root := hodgeTwoLthRoot T b
  root_eq := rfl
  root_pow := hodgeTwoLthRoot_pow T b

/-- Exact object-level condition for a root to lie in the completion. -/
def RootInCompletion
    (ζ : (AlgebraicClosure (Completion (qVPlace T b)))ˣ) : Prop :=
  ∃ u : (Completion (qVPlace T b))ˣ,
    algebraMap (Completion (qVPlace T b))
        (AlgebraicClosure (Completion (qVPlace T b))) (u : Completion (qVPlace T b)) =
      (ζ : AlgebraicClosure (Completion (qVPlace T b)))

/-- Exact completion-root gap: the actual algebraic-closure root is not
assumed to lie in the completion. -/
def TwoLthRootCompletionGap : Prop :=
  ¬ RootInCompletion (l := l) T b (hodgeTwoLthRoot T b)

/-- The algebraic-closure root data exists unconditionally. -/
theorem hodgeTwoLthRoot_available :
    Nonempty (HodgeTwoLthRootInterface T b) :=
  ⟨hodgeTwoLthRootInterface T b⟩

/-- The completion-root gap is exactly the negation of RootInCompletion; it is
not asserted, and no completion root is substituted. -/
theorem twoLthRootCompletionGap_iff :
    TwoLthRootCompletionGap (l := l) T b ↔
      ¬ RootInCompletion (l := l) T b (hodgeTwoLthRoot T b) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual

end
