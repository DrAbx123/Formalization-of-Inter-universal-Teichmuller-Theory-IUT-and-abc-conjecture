import tmp.sheaf.xif.paper.S502OddLiftObstructionActual

-- S509: the odd-lift condition is actual for the CHOSEN q-sqrt 2-torsion
-- point.  For an arbitrary 2-torsion point, selecting the q-sqrt class is
-- still an extra choice (paper EtTh only describes a special 2-torsion point).

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S509OddLiftChoiceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S485TateTwoTorsionQSqrtActual
open LeanFormal.IUT.XiFPaper.S494TateTwoTorsionConverseGapActual
open LeanFormal.IUT.XiFPaper.S502OddLiftObstructionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

theorem qHalfRootClass_sq_one :
    (QuotientGroup.mk (qHalfRootUnit T b) : FDeck T b) ^ 2 = 1 := by
  change (QuotientGroup.mk (qHalfRootUnit T b) : FDeck T b) ^ 2 = 1
  rw [pow_two, ← QuotientGroup.mk_mul]
  rw [show qHalfRootUnit T b * qHalfRootUnit T b = qUnit T b by
    rw [← pow_two, qHalfRootUnit_sq]]
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)

-- Actual odd-lift condition for the chosen q-sqrt point, k=1.
noncomputable def qSqrtOddLiftCondition : OddLiftCondition T b where
  x := QuotientGroup.mk (qHalfRootUnit T b)
  x_sq_one := qHalfRootClass_sq_one T b
  r := qHalfRootUnit T b
  r_class := rfl
  k := 1
  r_sq := by
    rw [zpow_one]
    exact (qHalfRootUnit_sq T b).symm
  k_odd := by norm_num
  root := qHalfRootUnit T b
  root_sq := qHalfRootUnit_sq T b
  point := qSqrtTwoTorsionPoint T b
  point_eq := rfl

-- Exact remaining choice for an arbitrary 2-torsion point: select the
-- q-sqrt component (paper EtTh's special 2-torsion point, if it matches).
structure QSqrtComponentSelection where
  point : ConversePoint T b
  point_two_torsion : point + point = 0
  point_ne_zero : point ≠ 0
  in_qSqrtClass : Prop
  root : (ACF T b)ˣ
  root_sq : root ^ 2 = qUnit T b
  point_eq : (fSidePointComparison T b).pointEquiv
    (QuotientGroup.mk root) = Multiplicative.ofAdd point

def QSqrtComponentSelectionRequired : Prop :=
  Nonempty (QSqrtComponentSelection T b)

#check qSqrtOddLiftCondition
#check QSqrtComponentSelection
#check QSqrtComponentSelectionRequired

end LeanFormal.IUT.XiFPaper.S509OddLiftChoiceActual

end