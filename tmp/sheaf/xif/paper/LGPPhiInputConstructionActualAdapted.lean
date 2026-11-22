import tmp.sheaf.xif.paper.LGPPhiInputFromAlgebraicClosureActual

-- LGP Phi/Input construction attempt: actual root normalization and scalar
-- theta action, plus exact remaining Phi/Input gap
--
-- What is actually proved here:
-- * the algebraic-closure 2l-th root has the correct 2l-th power
--   (rootNormalization), using the actual C3Roots root system;
-- * the theta-value scalar action on algebraic-closure units is an actual
--   monoid hom (multiplicative power action);
-- * the qV divisor exponents are actual qVFamily order data.
--
-- What is NOT fabricated: an LGP DivisorialMonoidOn/Input on the global
-- realified LGP Frobenioid, and the actual LGP tensor-packet action. Those are
-- recorded as an exact object-level gap.
-- WRITE-ONLY; no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.LGPPhiInputConstructionActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.LGPPhiInputFromAlgebraicClosureActual
open LeanFormal.IUT.XiFPaper.LGPPhiInputActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

-- Actual root normalization statement: the algebraic-closure 2l-th root
-- powers back to the embedded qV unit.
def LGPRootNormalization : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    lgpTwoLthRootAlgClosed T b ^ twoLExponent l =
      unitToAlgClosed (qVUnit T b)

theorem lgpRootNormalization_holds :
    LGPRootNormalization (l := l) T :=
  fun b => lgpTwoLthRootAlgClosed_pow T b

-- Actual scalar theta action on algebraic-closure units: the theta value
-- acts by the Gaussian power.
noncomputable def lgpThetaScalarAction
    (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) :
    (LGPAlgClosed (l := l) T b)ˣ →* (LGPAlgClosed (l := l) T b)ˣ where
  toFun x := x ^ (gaussExponent j.1).toNat
  map_one' := one_pow _
  map_mul' x y := mul_pow x y _

theorem lgpThetaScalarAction_apply
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value)
    (x : (LGPAlgClosed (l := l) T b)ˣ) :
    lgpThetaScalarAction T b j x = x ^ (gaussExponent j.1).toNat := rfl

-- Actual theta value is the scalar action applied to the 2l-th root.
theorem lgpThetaValueAlgClosed_eq_action
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    lgpThetaValueAlgClosed T b j =
      lgpThetaScalarAction T b j (lgpTwoLthRootAlgClosed T b) := rfl

-- Actual qV divisor data as a finitely supported exponent family.
noncomputable def lgpQVDivisorFinsupp :
    (Bad (nativePlaceSelection T) →₀ ℕ) := by
  classical
  exact ∑ b : Bad (nativePlaceSelection T),
    Finsupp.single b (lgpQVDivisorExponent T b)

theorem lgpQVDivisorFinsupp_apply
    (b : Bad (nativePlaceSelection T)) :
    lgpQVDivisorFinsupp T b = lgpQVDivisorExponent T b := by
  classical
  unfold lgpQVDivisorFinsupp
  simp

-- Exact object-level gap for the actual LGP Phi/Input: the q-side
-- DivisorialMonoidOn/Input and the algebraic-closure scalar action do not
-- by themselves produce the LGP global realified divisor monoid or its
-- tensor-packet action. All fields here are exact propositions/data, not
-- fabricated proofs.
structure LGPPhiInputConstructionGap where
  Phi : Iut.DivisorialMonoidOn (LGPBaseCategory.{u}) LGPIsFSM
  data : Iut.SourceModelFrobenioid.Input Phi
  qVDivisor : (Bad (nativePlaceSelection T) →₀ ℕ)
  qVDivisor_eq : qVDivisor = lgpQVDivisorFinsupp T
  tensorAction : Prop
  is_LGP : Prop

def LGPPhiInputConstructionObstruction : Prop :=
  Nonempty (LGPPhiInputConstructionGap.{u})

#check LGPRootNormalization
#check lgpRootNormalization_holds
#check lgpThetaScalarAction
#check lgpThetaScalarAction_apply
#check lgpThetaValueAlgClosed_eq_action
#check lgpQVDivisorFinsupp
#check LGPPhiInputConstructionGap
#check LGPPhiInputConstructionObstruction

end LeanFormal.IUT.XiFPaper.LGPPhiInputConstructionActualAdapted

end