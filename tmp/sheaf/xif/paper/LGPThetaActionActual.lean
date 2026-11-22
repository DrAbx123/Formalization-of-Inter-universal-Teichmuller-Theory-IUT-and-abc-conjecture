import tmp.sheaf.xif.paper.TwoLthRootKummerActual
import tmp.sheaf.xif.paper.LGPPhiInputActual

/-!
# LGP theta action/index data on the algebraic-closure 2l-th root

The actual 2l-th root of qVFamily q is taken in the algebraic closure of the
completion (TwoLthRootKummerActual.hodgeTwoLthRoot), not in the completion.
Using this root, this file constructs the actual theta-value action/index data

  j |-> hodgeTwoLthRoot^(j^2)

for j in SignedLabel l.value, where j^2 is the actual gaussExponent.

The action values are units in AlgebraicClosure (Completion place).  The roots
are determined up to the actual mu_{2l} set, and the theta values inherit the
corresponding mu ambiguity (zeta^(j^2)).

The LGP Phi/Input itself (the DivisorialMonoidOn and SourceModelFrobenioid.Input
carrying the LGP theta action) is not constructed here; the exact object-level
gap is the existing LGPPhiInputActual.LGPPhiInputObstruction, recorded below and
not replaced by a completion root or a value-layer surrogate.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.LGPThetaActionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.LGPPhiInputActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual LGP theta label index. -/
abbrev LGPThetaIndex (l : PrimeGeFive) : Type :=
  SignedLabel l.value

/-- The actual gauss exponent j^2 as an action index. -/
def lgpThetaExponent (l : PrimeGeFive) (j : LGPThetaIndex l) : Nat :=
  (gaussExponent j.1).toNat

/-- The actual theta value root^(j^2) in the algebraic closure. -/
noncomputable def lgpThetaValue
    (j : LGPThetaIndex l) :
    (AlgebraicClosure (Completion (qVPlace T b)))ˣ :=
  (hodgeTwoLthRoot T b) ^ lgpThetaExponent l j

/-- The theta value is the Hodge root raised to the actual gauss exponent. -/
@[simp] theorem lgpThetaValue_eq
    (j : LGPThetaIndex l) :
    lgpThetaValue T b j =
      (hodgeTwoLthRoot T b) ^ lgpThetaExponent l j :=
  rfl

/-- The 2l-th power of the theta value is qV^(j^2), still in the algebraic
closure. -/
theorem lgpThetaValue_pow_twoL
    (j : LGPThetaIndex l) :
    lgpThetaValue T b j ^ (2 * l.value) =
      qVAlgClosedUnit T b ^ lgpThetaExponent l j := by
  unfold lgpThetaValue
  calc
    (hodgeTwoLthRoot T b ^ lgpThetaExponent l j) ^ (2 * l.value)
        = hodgeTwoLthRoot T b ^
            (lgpThetaExponent l j * (2 * l.value)) := by rw [← pow_mul]
    _ = hodgeTwoLthRoot T b ^
            ((2 * l.value) * lgpThetaExponent l j) := by rw [Nat.mul_comm]
    _ = (hodgeTwoLthRoot T b ^ (2 * l.value)) ^
            lgpThetaExponent l j := by rw [← pow_mul]
    _ = qVAlgClosedUnit T b ^ lgpThetaExponent l j := by
          rw [hodgeTwoLthRoot_pow]

/-- Actual mu_{2l} ambiguity of the theta value: replacing the root by zeta *
root multiplies the theta value by zeta^(j^2). -/
theorem lgpThetaValue_mu_shift
    (ζ : (AlgebraicClosure (Completion (qVPlace T b)))ˣ)
    (hζ : ζ ∈ muTwoLAlgClosed (l := l) T b)
    (j : LGPThetaIndex l) :
    (ζ * hodgeTwoLthRoot T b) ^ lgpThetaExponent l j =
      ζ ^ lgpThetaExponent l j * lgpThetaValue T b j := by
  rw [mul_pow]
  rfl

/-- Indexed theta action data on the actual algebraic-closure root. -/
structure LGPThetaActionData where
  rootSystem : NatRootSystem (qVAlgClosedUnit T b)
  root : (AlgebraicClosure (Completion (qVPlace T b)))ˣ
  root_eq : root = rootSystem.root (2 * l.value)
  index : LGPThetaIndex l -> Nat
  value : LGPThetaIndex l -> (AlgebraicClosure (Completion (qVPlace T b)))ˣ
  value_eq : ∀ j, value j = root ^ index j
  value_eq_hodge : ∀ j, value j = lgpThetaValue T b j
  mu_shift : ∀ (ζ : (AlgebraicClosure (Completion (qVPlace T b)))ˣ),
    ζ ∈ muTwoLAlgClosed (l := l) T b -> ∀ j,
      (ζ * root) ^ index j = ζ ^ index j * value j

/-- Actual theta action data from the Hodge root system. -/
noncomputable def lgpThetaActionData :
    LGPThetaActionData T b where
  rootSystem := hodgeTwoLRootSystem T b
  root := hodgeTwoLthRoot T b
  root_eq := rfl
  index := lgpThetaExponent l
  value := lgpThetaValue T b
  value_eq := by
    intro j
    rfl
  value_eq_hodge := by
    intro j
    rfl
  mu_shift := by
    intro ζ hζ j
    exact lgpThetaValue_mu_shift T b ζ hζ j

/-- The actual LGP theta action data exists. -/
theorem lgpThetaActionData_available :
    Nonempty (LGPThetaActionData T b) :=
  ⟨lgpThetaActionData T b⟩

/-- Exact object-level gap for the LGP Phi/Input: the actual
DivisorialMonoidOn and SourceModelFrobenioid.Input carrying the LGP theta action
are not constructed. This is exactly the existing LGPPhiInput obstruction, not
a completion-root or value-layer replacement. -/
def LGPThetaActionPhiGap : Prop :=
  LGPPhiInputObstruction.{u}

end LeanFormal.IUT.XiFPaper.LGPThetaActionActual

end
