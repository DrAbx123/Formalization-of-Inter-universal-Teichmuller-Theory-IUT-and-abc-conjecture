import tmp.sheaf.xif.paper.S479TwoTorsionParityGapActual
import tmp.sheaf.n8.closure.NativeSourceReductionActual
import LeanFormal.IUT.Foundations.Geometry.TatePointQuotientBoundary

-- S485: actual F-side Tate comparison + actual square root of q gives an
-- actual 2-torsion point.  The converse/order-parity is exact missing.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S485TateTwoTorsionQSqrtActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S479TwoTorsionParityGapActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

abbrev FPlace : NumberField.FinitePlace T.arithmetic.F :=
  (nativeBadLift T).lift b
abbrev KF : Type := Completion (FPlace T b)
abbrev ACF : Type := AlgebraicClosure (KF T b)

noncomputable def qUnit : (ACF T b)ˣ :=
  tateParameterUnit (FPlace T b) (qVFamily T b).q (qVFamily T b).q_ne_zero

noncomputable def qHalfRootElement : ACF T b :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (qUnit T b : ACF T b)
    (by norm_num : 0 < 2))

theorem qHalfRootElement_sq :
    qHalfRootElement T b ^ 2 = (qUnit T b : ACF T b) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (qUnit T b : ACF T b)
    (by norm_num : 0 < 2))

theorem qHalfRootElement_ne_zero : qHalfRootElement T b ≠ 0 := by
  intro h
  have hsq := qHalfRootElement_sq T b
  rw [h, zero_pow (by norm_num : (2 : Nat) ≠ 0)] at hsq
  exact (Units.ne_zero (qUnit T b)) hsq.symm

noncomputable def qHalfRootUnit : (ACF T b)ˣ :=
  Units.mk0 (qHalfRootElement T b) (qHalfRootElement_ne_zero T b)

theorem qHalfRootUnit_sq :
    qHalfRootUnit T b ^ 2 = qUnit T b := by
  ext
  simpa [qHalfRootUnit] using qHalfRootElement_sq T b

abbrev FDeck : Type :=
  TatePointComparison.DeckQuotient (place := FPlace T b) (parameter := qVFamily T b)

noncomputable def fSidePointComparison :
    TatePointComparison T.arithmetic.curve (FPlace T b) (qVFamily T b) :=
  (nativeBadTateWitness T (nativeBadLift T) b).comparison.points

noncomputable def qSqrtTwoTorsionPoint :
    (T.arithmetic.curve.baseChange (Completion (FPlace T b))).AlgebraicClosurePoint :=
  (fSidePointComparison T b).pointEquiv
    (QuotientGroup.mk (qHalfRootUnit T b) : FDeck T b) |>.toAdd

theorem qSqrtTwoTorsionPoint_double :
    qSqrtTwoTorsionPoint T b + qSqrtTwoTorsionPoint T b = 0 := by
  let comp := fSidePointComparison T b
  let x : FDeck T b := QuotientGroup.mk (qHalfRootUnit T b)
  have hx : x ^ 2 = 1 := by
    change (QuotientGroup.mk (qHalfRootUnit T b) : FDeck T b) ^ 2 = 1
    rw [pow_two, ← QuotientGroup.mk_mul]
    rw [show qHalfRootUnit T b * qHalfRootUnit T b = qUnit T b by
      rw [← pow_two, qHalfRootUnit_sq]]
    exact (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.mem_zpowers _)
  have hmap : comp.pointEquiv x ^ 2 = 1 := by
    have h := map_pow comp.pointEquiv x 2
    rw [hx, map_one] at h
    exact h.symm
  have hto := congrArg Multiplicative.toAdd hmap
  simpa [qSqrtTwoTorsionPoint, comp, x, pow_two] using hto
structure QSqrtTwoTorsionData where
  root : (ACF T b)ˣ
  root_sq : root ^ 2 = qUnit T b
  point : (T.arithmetic.curve.baseChange (Completion (FPlace T b))).AlgebraicClosurePoint
  point_eq : (fSidePointComparison T b).pointEquiv (QuotientGroup.mk root) =
    Multiplicative.ofAdd point
  point_two_torsion : point + point = 0

noncomputable def qSqrtTwoTorsionData : QSqrtTwoTorsionData T b where
  root := qHalfRootUnit T b
  root_sq := qHalfRootUnit_sq T b
  point := qSqrtTwoTorsionPoint T b
  point_eq := rfl
  point_two_torsion := qSqrtTwoTorsionPoint_double T b

-- Exact missing converse: a nonzero 2-torsion point giving q^(1/2).
structure TwoTorsionToQSqrtConverseGap where
  point : (T.arithmetic.curve.baseChange (Completion (FPlace T b))).AlgebraicClosurePoint
  point_two_torsion : point + point = 0
  point_ne_zero : point ≠ 0
  root : (ACF T b)ˣ
  root_sq : root ^ 2 = qUnit T b
  point_eq_root : (fSidePointComparison T b).pointEquiv
    (QuotientGroup.mk root) = Multiplicative.ofAdd point

def TwoTorsionToQSqrtConverseGapRequired : Prop :=
  Nonempty (TwoTorsionToQSqrtConverseGap T b)

#check qUnit
#check qHalfRootUnit
#check fSidePointComparison
#check qSqrtTwoTorsionPoint_double
#check qSqrtTwoTorsionData
#check TwoTorsionToQSqrtConverseGap

end LeanFormal.IUT.XiFPaper.S485TateTwoTorsionQSqrtActual

end