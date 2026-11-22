import tmp.sheaf.xif.paper.S342QVFamilyRootImpossibleActual

/-! # S795: order semantics and the Def 3.1(c) / q[2u] tension

`FinitePlaceQCandidate.order` is actually defined as the positive valuation
exponent: order = Int.toNat(-toAdd(unzero(v q))).  Thus in the ordinary
completion a 2l-th root forces 2l | order, while Def 3.1(c) makes l coprime to
the order.  S342 proves no such completion root exists.  Example 3.2(iv)
places q[2u] in O^tri(TX_v), the log/root-stack, not in ordinary O^tri_{K_v}.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S795OrderSemanticsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.S342QVFamilyRootImpossibleActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual qVFamily order is the positive valuation exponent. -/
theorem qVFamily_order_eq_valuation :
    (qVFamily T b).order = Int.toNat (qVFamily T b).exponent := rfl

/-- The order is prime to l (Def 3.1(c)). -/
theorem qVFamily_order_coprime_actual :
    Nat.Coprime (qVFamily T b).order l.value :=
  qVFamily_order_coprime (l := l) T b

/-- No ordinary completion 2l-th-root data. -/
theorem ordinaryTwoLRootData_impossible :
    ¬ Nonempty (TwoLthRootData T b) :=
  twoLthRootData_impossible (l := l) T b

/-- Def 3.1(c) together with an ordinary completion q[2u] root is impossible. -/
def Def31cOrdinaryRootConflict : Prop :=
  Nat.Coprime (qVFamily T b).order l.value ∧ Nonempty (TwoLthRootData T b)

theorem def31cOrdinaryRootConflict_false :
    ¬ Def31cOrdinaryRootConflict (l := l) T b := by
  rintro ⟨hc, hroot⟩
  exact ordinaryTwoLRootData_impossible (l := l) T b hroot

/-- If order were not the valuation, then qVFamily.order would not be the
paper q-parameter order.  This records the alternative semantic branch. -/
def OrderIsPaperValuation : Prop :=
  (qVFamily T b).order = Int.toNat (qVFamily T b).exponent

theorem orderIsPaperValuation_actual :
    OrderIsPaperValuation (l := l) T b :=
  rfl

end LeanFormal.IUT.XiFPaper.S795OrderSemanticsActual
end
