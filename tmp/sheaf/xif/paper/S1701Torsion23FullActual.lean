import tmp.sheaf.xif.paper.S1700ThreeTorsionExhaustionActual
import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion

/-! # S1701: full Torsion23Rational over the S1687 field

`Torsion23Rational` is `AllNTorsionRational 6`: every 6-torsion point over an
algebraic closure descends to the base field.  This file proves the group-law
reduction: if all 2-torsion and all 3-torsion descend, then all 6-torsion
descends, via P = 3P - 2P.  The two remaining inputs are the 2-torsion and
3-torsion base-change classifications.

No sorry, axiom or fake descent map is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1701Torsion23FullActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1700ThreeTorsionExhaustionActual
open WeierstrassCurve WeierstrassCurve.Affine

/-- The generic E[6] decomposition: if 2-torsion and 3-torsion descend, then
6-torsion descends.  Uses `P = 3•P - 2•P` and additivity of base change. -/
theorem S1701_allSix_of_two_three {F : Type*} [Field F]
    (X : PuncturedEllipticCurve F)
    (h2 : X.AllNTorsionRational 2) (h3 : X.AllNTorsionRational 3) :
    X.AllNTorsionRational 6 := by
  classical
  intro P h6
  let A : (X.curve.toAffine.baseChange (AlgebraicClosure F)).Point := (3 : ℤ) • P
  let B : (X.curve.toAffine.baseChange (AlgebraicClosure F)).Point := (2 : ℤ) • P
  have h2A : (2 : ℤ) • A = 0 := by
    dsimp [A]
    rw [← mul_zsmul]
    norm_num
    exact h6
  have h3B : (3 : ℤ) • B = 0 := by
    dsimp [B]
    rw [← mul_zsmul]
    norm_num
    exact h6
  obtain ⟨Q, hQ⟩ := h2 A h2A
  obtain ⟨R, hR⟩ := h3 B h3B
  refine ⟨(Q : (X.curve.toAffine⁄F).Point) - (R : (X.curve.toAffine⁄F).Point), ?_⟩
  erw [map_sub, hQ, hR]
  dsimp [A, B]
  rw [sub_eq_add_neg, ← sub_zsmul]
  norm_num

/-- The actual 2-torsion descent statement over the S1687 field. -/
def S1701Torsion2Rational : Prop :=
  (S1667Punctured.baseChange S1687Field).AllNTorsionRational 2

/-- The actual 3-torsion descent statement over the S1687 field. -/
def S1701Torsion3Rational : Prop :=
  (S1667Punctured.baseChange S1687Field).AllNTorsionRational 3

/-- Full 6-torsion descent from the two base-change classifications. -/
theorem S1701Torsion23_of_parts
    (h2 : S1701Torsion2Rational) (h3 : S1701Torsion3Rational) :
    PuncturedEllipticCurve.Torsion23Rational
      (S1667Punctured.baseChange S1687Field) :=
  S1701_allSix_of_two_three (S1667Punctured.baseChange S1687Field) h2 h3

/-- Exact first missing input for the full Torsion23Rational: the 2-torsion
and 3-torsion base-change classifications. -/
def S1701FirstMissing : Prop :=
  S1701Torsion2Rational ∧ S1701Torsion3Rational

#check S1701_allSix_of_two_three
#check S1701Torsion2Rational
#check S1701Torsion3Rational
#check S1701Torsion23_of_parts

end LeanFormal.IUT.XiFPaper.S1701Torsion23FullActual
end
