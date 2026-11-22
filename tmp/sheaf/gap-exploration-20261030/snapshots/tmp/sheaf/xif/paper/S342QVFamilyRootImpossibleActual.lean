import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4TateQIdentification
import tmp.sheaf.xif.paper.S330QVFamilyRootCardActual
import tmp.sheaf.xif.paper.TwoLthRootQVActual

/-! # S342: qVFamily 2l-th-root card is impossible from the source order

The D4 Tate-q identification module proves that any QParameterTwoLRootCard
forces l to divide the parameter order, contradicting clause (c)
Nat.Coprime parameter.order l.  The actual QVFamily parameter carries exactly
such a coprime order from its SourceTateComparisonWitness.

Hence there is no completion 2l-th-root card for qVFamily, and no
TwoLthRootData/NatRootSystem in the completion.  The obstruction is the
valuation/order one; Kummer surjectivity on principal units cannot remove it.

No L, no fake root, no inequality.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S342QVFamilyRootImpossibleActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource.PlaceQParameterUniformization
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.S330QVFamilyRootCardActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual qVFamily Tate comparison witness, chosen exactly as in qVFamily. -/
noncomputable def qVFamilyTateWitness :
    SourceTateComparisonWitness T.arithmetic (qVFamilyPlace T b) :=
  Classical.choice
    (T.clauseB.q_comparison ((nativeBadLift T).lift b)
      (by
        rw [(nativeBadLift T).lift_comap b]
        exact b.2))

/-- The actual qVFamily order is prime to l, from the Clause-B witness. -/
theorem qVFamily_order_coprime :
    Nat.Coprime (qVFamily T b).order l.value := by
  rw [qVFamily_eq_comparisonParameter]
  exact (qVFamilyTateWitness T b).order_coprime

/-- Any completion 2l-th-root card forces the order to be non-coprime to l;
the actual qVFamily order is coprime. -/
theorem qVFamilyTwoLRootCard_impossible :
    ¬ Nonempty (QVFamilyTwoLRootCard (T := T) (b := b)) := by
  rintro ⟨card⟩
  exact (twoLRootCard_parameter_order_not_coprime (l := l)
    (place := qVFamilyPlace T b) (parameter := qVFamily T b) card)
    (qVFamily_order_coprime T b)

/-- The exact missing Kummer/Hensel input of S330 is in fact inconsistent:
it is the same card gap. -/
theorem missingKummerHenselInput_impossible :
    ¬ MissingKummerHenselInput (T := T) (b := b) := by
  rw [missingKummerHenselInput_iff]
  exact qVFamilyTwoLRootCard_impossible T b

/-- A TwoLthRootData in the completion would give a card, hence is impossible. -/
noncomputable def cardOfTwoLthRootData
    (D : TwoLthRootData T b) :
    QVFamilyTwoLRootCard (T := T) (b := b) where
  root := (D.root : Completion (qVFamilyPlace T b))
  root_ne_zero := Units.ne_zero D.root
  root_pow := by
    have h := congrArg
      (fun u : (Completion (qVFamilyPlace T b))ˣ =>
        (u : Completion (qVFamilyPlace T b))) D.root_pow
    simpa [twoLExponent, qVUnit] using h

/-- There is no actual completion TwoLthRootData for qVFamily. -/
theorem twoLthRootData_impossible :
    ¬ Nonempty (TwoLthRootData T b) := by
  rintro ⟨D⟩
  exact qVFamilyTwoLRootCard_impossible T b ⟨cardOfTwoLthRootData T b D⟩

/-- Consequently there is no NatRootSystem qVUnit in the completion. -/
theorem natRootSystem_impossible :
    ¬ Nonempty (NatRootSystem (qVUnit T b)) := by
  rintro ⟨R⟩
  exact twoLthRootData_impossible T b
    ⟨twoLthRootDataOfRootSystem T b R⟩

end LeanFormal.IUT.XiFPaper.S342QVFamilyRootImpossibleActual

end
