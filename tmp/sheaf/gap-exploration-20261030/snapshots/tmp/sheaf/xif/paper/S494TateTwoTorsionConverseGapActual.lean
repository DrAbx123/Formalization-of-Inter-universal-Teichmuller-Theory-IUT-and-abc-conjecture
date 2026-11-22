import tmp.sheaf.xif.paper.S485TateTwoTorsionQSqrtActual

-- S494 audit: quotient/pointEquiv gives only a class; the missing converse
-- needs a lift with odd q-exponent (or directly a root with root^2=qUnit).

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S494TateTwoTorsionConverseGapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S485TateTwoTorsionQSqrtActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

abbrev ConversePoint : Type :=
  (T.arithmetic.curve.baseChange (Completion (FPlace T b))).AlgebraicClosurePoint

-- Exact quotient-level data: the class gives an exponent k with
-- qUnit^k = (lift)^2; the converse needs k odd (or a root directly).
structure TwoTorsionQuotientLiftData where
  point : ConversePoint T b
  point_two_torsion : point + point = 0
  point_ne_zero : point ≠ 0
  x : FDeck T b
  x_sq_one : x ^ 2 = 1
  x_ne_one : x ≠ 1
  r : (ACF T b)ˣ
  r_class : QuotientGroup.mk r = x
  k : ℤ
  r_sq : qUnit T b ^ k = r ^ 2
  k_odd : Odd k
  root : (ACF T b)ˣ
  root_sq : root ^ 2 = qUnit T b
  point_eq : (fSidePointComparison T b).pointEquiv
    (QuotientGroup.mk root) = Multiplicative.ofAdd point

def TwoTorsionQuotientLiftDataRequired : Prop :=
  Nonempty (TwoTorsionQuotientLiftData T b)

-- The only direction actually supplied by S485: root -> 2-torsion point.
theorem root_to_twoTorsion
    (root : (ACF T b)ˣ) (hroot : root ^ 2 = qUnit T b) :
    let P := ((fSidePointComparison T b).pointEquiv
      (QuotientGroup.mk root : FDeck T b)).toAdd
    P + P = 0 := by
  let comp := fSidePointComparison T b
  let x : FDeck T b := QuotientGroup.mk root
  have hx : x ^ 2 = 1 := by
    change (QuotientGroup.mk root : FDeck T b) ^ 2 = 1
    rw [pow_two, ← QuotientGroup.mk_mul]
    rw [show root * root = qUnit T b by
      rw [← pow_two, hroot]]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
  have hmap : comp.pointEquiv x ^ 2 = 1 := by
    have h := map_pow comp.pointEquiv x 2
    rw [hx, map_one] at h
    exact h.symm
  have hto := congrArg Multiplicative.toAdd hmap
  simpa [comp, x, pow_two] using hto

#check TwoTorsionQuotientLiftData
#check TwoTorsionQuotientLiftDataRequired
#check root_to_twoTorsion

end LeanFormal.IUT.XiFPaper.S494TateTwoTorsionConverseGapActual

end