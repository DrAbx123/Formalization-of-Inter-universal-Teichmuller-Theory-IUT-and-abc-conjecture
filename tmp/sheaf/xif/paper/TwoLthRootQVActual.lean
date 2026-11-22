import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import LeanFormal.IUT.IUTII.Kummer.NatRootSystem

/-!
# 2l-th roots of the actual q_v family in the completion

For each native bad place b, the actual q family is

  qVFamily T b : FinitePlaceQCandidate ((nativeBadLift T).lift b),

with q in the actual completion of the finite F-place over b.  The q-pilot
theta input needs a 2l-th root q_v^{1/2l}, determined only up to mu_{2l}.

This file constructs the root conditionally from an actual compatible root
system in the completion:

  R : NatRootSystem (qVUnit T b).

With such an R, the root is R.root (2 * l.value), and it satisfies

  (R.root (2*l.value)) ^ (2*l.value) = qVUnit T b.

Two root systems give roots whose ratio lies in the actual mu_{2l} root set
{zeta | zeta ^ (2*l.value) = 1}.  This is the actual mu_{2l} ambiguity.

The completion is not algebraically closed; the tree does not construct
NatRootSystem (qVUnit T b) for a general q.  The exact missing root-existence
datum is recorded as TwoLRootExistenceGap.  No root is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.TwoLthRootQVActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual q_v as a unit in its completion. -/
noncomputable def qVUnit :
    (Completion ((nativeBadLift T).lift b))ˣ :=
  Units.mk0 (qVFamily T b).q (qVFamily T b).q_ne_zero

/-- The q_v unit is the qVFamily q. -/
@[simp] theorem qVUnit_apply :
    (qVUnit T b : Completion ((nativeBadLift T).lift b)) =
      (qVFamily T b).q :=
  rfl

/-- The exponent 2l. -/
def twoLExponent (l : PrimeGeFive) : Nat := 2 * l.value

/-- The actual mu_{2l} root set in the completion. -/
def muTwoLRoots : Set (Completion ((nativeBadLift T).lift b))ˣ :=
  {ζ | ζ ^ twoLExponent l = 1}

/-- The actual 2l-th root obtained from a compatible root system in the
completion. -/
noncomputable def twoLthRoot
    (R : NatRootSystem (qVUnit T b)) :
    (Completion ((nativeBadLift T).lift b))ˣ :=
  R.root (twoLExponent l)

/-- The constructed 2l-th root has the correct power. -/
theorem twoLthRoot_pow
    (R : NatRootSystem (qVUnit T b)) :
    twoLthRoot T b R ^ twoLExponent l = qVUnit T b := by
  unfold twoLthRoot
  exact R.pow_self (twoLExponent l) (by
    unfold twoLExponent
    exact Nat.mul_ne_zero (by norm_num) l.prime.ne_zero)

/-- The completion element of the constructed root has 2l-th power q_v. -/
theorem twoLthRoot_completion_pow
    (R : NatRootSystem (qVUnit T b)) :
    (twoLthRoot T b R : Completion ((nativeBadLift T).lift b)) ^
        twoLExponent l =
      (qVFamily T b).q := by
  rw [← Units.val_pow_eq_pow_val, twoLthRoot_pow, qVUnit_apply]

/-- Two 2l-th roots of the same q have quotient in the actual mu_{2l} root set. -/
theorem twoLthRoot_ratio_mem_mu
    (R R' : NatRootSystem (qVUnit T b)) :
    (R'.root (twoLExponent l) / R.root (twoLExponent l)) ∈
      muTwoLRoots (l := l) T b := by
  unfold muTwoLRoots
  simp only [Set.mem_setOf_eq]
  rw [div_pow, R'.pow_self (twoLExponent l) (by
      unfold twoLExponent
      exact Nat.mul_ne_zero (by norm_num) l.prime.ne_zero),
    R.pow_self (twoLExponent l) (by
      unfold twoLExponent
      exact Nat.mul_ne_zero (by norm_num) l.prime.ne_zero)]
  simp

/-- Actual root data: a completion unit with a 2l-th power equal to q_v. -/
structure TwoLthRootData where
  root : (Completion ((nativeBadLift T).lift b))ˣ
  root_pow : root ^ twoLExponent l = qVUnit T b

/-- Conditional construction of the root data from a compatible completion root
system. -/
noncomputable def twoLthRootDataOfRootSystem
    (R : NatRootSystem (qVUnit T b)) : TwoLthRootData T b where
  root := twoLthRoot T b R
  root_pow := twoLthRoot_pow T b R

/-- The exact missing root-existence datum: a compatible root system for the
actual q_v unit in the completion. -/
def TwoLRootExistenceGap : Prop :=
  Nonempty (NatRootSystem (qVUnit T b))

/-- Conditional actual root: the root system is the only missing input. -/
theorem twoLthRootData_exists_of_rootSystem
    (R : NatRootSystem (qVUnit T b)) :
    Nonempty (TwoLthRootData T b) :=
  ⟨twoLthRootDataOfRootSystem T b R⟩

/-- The constructed root is determined up to the actual mu_{2l} root set. -/
theorem twoLthRoot_ambiguity
    (R R' : NatRootSystem (qVUnit T b)) :
    ∃ ζ ∈ muTwoLRoots (l := l) T b,
      R'.root (twoLExponent l) = ζ * R.root (twoLExponent l) := by
  refine ⟨R'.root (twoLExponent l) / R.root (twoLExponent l),
    twoLthRoot_ratio_mem_mu T b R R', ?_⟩
  rw [div_mul_cancel]

end LeanFormal.IUT.XiFPaper.TwoLthRootQVActual

end
