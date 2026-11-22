import tmp.sheaf.xif.paper.S1705AllTorsionRationalActual

/-! # S1706: F-rational torsion cardinalities

The remaining S1705 inputs are `Nat.card E_F[2] = 4` and
`Nat.card E_F[3] = 9`.  This file proves the 2-torsion cardinality from the
three explicit rational points `(0,0)`, `(1,0)`, `(-125/64,0)` plus zero,
and records the exact 3-torsion count input.  No fake Nonempty is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1706FCardActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1702AllTorsionRationalActual
open LeanFormal.IUT.XiFPaper.S1704TorsionCardActual
open LeanFormal.IUT.XiFPaper.S1705AllTorsionRationalActual
open WeierstrassCurve WeierstrassCurve.Affine

local instance : DecidableEq S1705F := Classical.decEq _
local instance : DecidableEq S1702Closure := Classical.decEq _
open LeanFormal.IUT.XiFPaper.S1701Torsion23FullActual

def S1706T0F : S1705FPoint :=
  Affine.Point.some (W' := S1705X.curve.toAffine) 0 0
    (by
      have h := (WeierstrassCurve.Affine.map_nonsingular
        (W := S1667Curve.toAffine) (f := Algebra.ofId ℚ S1705F)
        (by exact (algebraMap ℚ S1705F).injective) 0 0).mpr S1667_nonsingular_zero
      simpa using h)

def S1706T1F : S1705FPoint :=
  Affine.Point.some (W' := S1705X.curve.toAffine) 1 0
    (by
      change (S1667Curve.toAffine.map (algebraMap ℚ S1705F)).Nonsingular 1 0
      have h := (WeierstrassCurve.Affine.map_nonsingular
        (W := S1667Curve.toAffine) (f := Algebra.ofId ℚ S1705F)
        (by exact (algebraMap ℚ S1705F).injective) 1 0).mpr S1667_nonsingular_one
      simpa using h)

def S1706T2F : S1705FPoint :=
  Affine.Point.some (W' := S1705X.curve.toAffine) (-125/64) 0
    (by
      change (S1667Curve.toAffine.map (algebraMap ℚ S1705F)).Nonsingular (-125/64) 0
      have h := (WeierstrassCurve.Affine.map_nonsingular
        (W := S1667Curve.toAffine) (f := Algebra.ofId ℚ S1705F)
        (by exact (algebraMap ℚ S1705F).injective) (-125/64) 0).mpr S1667_nonsingular_lambda
      simpa using h)

theorem S1706T0F_two : (2 : ℤ) • S1706T0F = 0 := by
  rw [show (2 : ℤ) • S1706T0F = S1706T0F + S1706T0F by rw [two_zsmul]]
  apply Affine.Point.add_self_of_Y_eq
  simp [S1706T0F, S1705X, S1667Punctured, S1667Curve,
    WeierstrassCurve.baseChange, WeierstrassCurve.map,
    WeierstrassCurve.Affine.negY]

theorem S1706T1F_two : (2 : ℤ) • S1706T1F = 0 := by
  rw [show (2 : ℤ) • S1706T1F = S1706T1F + S1706T1F by rw [two_zsmul]]
  apply Affine.Point.add_self_of_Y_eq
  simp [S1706T1F, S1705X, S1667Punctured, S1667Curve,
    WeierstrassCurve.baseChange, WeierstrassCurve.map,
    WeierstrassCurve.Affine.negY]

theorem S1706T2F_two : (2 : ℤ) • S1706T2F = 0 := by
  rw [show (2 : ℤ) • S1706T2F = S1706T2F + S1706T2F by rw [two_zsmul]]
  apply Affine.Point.add_self_of_Y_eq
  simp [S1706T2F, S1705X, S1667Punctured, S1667Curve,
    WeierstrassCurve.baseChange, WeierstrassCurve.map,
    WeierstrassCurve.Affine.negY]

theorem S1706T0F_ne_T1F : S1706T0F ≠ S1706T1F := by
  intro h
  have h' := Affine.Point.some.inj h
  norm_num at h'

theorem S1706T0F_ne_T2F : S1706T0F ≠ S1706T2F := by
  intro h
  have h' := Affine.Point.some.inj h
  norm_num at h'

theorem S1706T1F_ne_T2F : S1706T1F ≠ S1706T2F := by
  intro h
  have h' := Affine.Point.some.inj h
  norm_num at h'

theorem S1706T0F_ne_zero : S1706T0F ≠ 0 :=
  Affine.Point.some_ne_zero (by
    have h := (WeierstrassCurve.Affine.map_nonsingular
      (W := S1667Curve.toAffine) (f := Algebra.ofId ℚ S1705F)
      (by exact (algebraMap ℚ S1705F).injective) 0 0).mpr S1667_nonsingular_zero
    simpa using h)

theorem S1706T1F_ne_zero : S1706T1F ≠ 0 :=
  Affine.Point.some_ne_zero (by
    change (S1667Curve.toAffine.map (algebraMap ℚ S1705F)).Nonsingular 1 0
    have h := (WeierstrassCurve.Affine.map_nonsingular
      (W := S1667Curve.toAffine) (f := Algebra.ofId ℚ S1705F)
      (by exact (algebraMap ℚ S1705F).injective) 1 0).mpr S1667_nonsingular_one
    simpa using h)

theorem S1706T2F_ne_zero : S1706T2F ≠ 0 :=
  Affine.Point.some_ne_zero (by
    change (S1667Curve.toAffine.map (algebraMap ℚ S1705F)).Nonsingular (-125/64) 0
    have h := (WeierstrassCurve.Affine.map_nonsingular
      (W := S1667Curve.toAffine) (f := Algebra.ofId ℚ S1705F)
      (by exact (algebraMap ℚ S1705F).injective) (-125/64) 0).mpr S1667_nonsingular_lambda
    simpa using h)

noncomputable def S1706FourFun : Option (Fin 3) → S1705FTorsion2
  | none => ⟨0, zsmul_zero 2⟩
  | some 0 => ⟨S1706T0F, S1706T0F_two⟩
  | some 1 => ⟨S1706T1F, S1706T1F_two⟩
  | some 2 => ⟨S1706T2F, S1706T2F_two⟩

theorem S1706FourFun_injective : Function.Injective S1706FourFun := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some j =>
      fin_cases j
      · exact (S1706T0F_ne_zero (congrArg Subtype.val h).symm).elim
      · exact (S1706T1F_ne_zero (congrArg Subtype.val h).symm).elim
      · exact (S1706T2F_ne_zero (congrArg Subtype.val h).symm).elim
  | some i =>
    cases b with
    | none =>
      fin_cases i
      · exact (S1706T0F_ne_zero (congrArg Subtype.val h)).elim
      · exact (S1706T1F_ne_zero (congrArg Subtype.val h)).elim
      · exact (S1706T2F_ne_zero (congrArg Subtype.val h)).elim
    | some j =>
      fin_cases i <;> fin_cases j
      · rfl
      · exact (S1706T0F_ne_T1F (congrArg Subtype.val h)).elim
      · exact (S1706T0F_ne_T2F (congrArg Subtype.val h)).elim
      · exact (S1706T0F_ne_T1F (congrArg Subtype.val h).symm).elim
      · rfl
      · exact (S1706T1F_ne_T2F (congrArg Subtype.val h)).elim
      · exact (S1706T0F_ne_T2F (congrArg Subtype.val h).symm).elim
      · exact (S1706T1F_ne_T2F (congrArg Subtype.val h).symm).elim
      · rfl

theorem S1706TwoTorsionFCard_ge : 4 ≤ Nat.card S1705FTorsion2 := by
  have hK : Nat.card S1705KTorsion2 = 4 := by
    change Nat.card { P : S1702ClosurePoint // (2 : ℤ) • P = 0 } = 4
    exact S1704TorsionCardActual.twoTorsionCard
  haveI : Finite S1705KTorsion2 :=
    (Nat.card_ne_zero.mp (by rw [hK]; norm_num)).2
  haveI : Finite S1705FTorsion2 :=
    Finite.of_injective S1705Descent2 S1705Descent2_injective
  have h := Nat.card_le_card_of_injective S1706FourFun S1706FourFun_injective
  simpa using h

theorem S1706TwoTorsionFCard_le : Nat.card S1705FTorsion2 ≤ 4 := by
  have hK : Nat.card S1705KTorsion2 = 4 := by
    change Nat.card { P : S1702ClosurePoint // (2 : ℤ) • P = 0 } = 4
    exact S1704TorsionCardActual.twoTorsionCard
  haveI : Finite S1705KTorsion2 :=
    (Nat.card_ne_zero.mp (by rw [hK]; norm_num)).2
  simpa [hK] using
    Nat.card_le_card_of_injective S1705Descent2 S1705Descent2_injective

theorem S1706TwoTorsionFCard : S1705TwoTorsionFCard := by
  apply le_antisymm S1706TwoTorsionFCard_le S1706TwoTorsionFCard_ge

/-- Exact remaining input: F-rational 3-torsion cardinality. -/
def S1706ThreeTorsionFCardMissing : Prop :=
  S1705ThreeTorsionFCard

theorem S1706Torsion2Rational : S1701Torsion2Rational :=
  S1705AllNTorsion2_of_card S1706TwoTorsionFCard

theorem S1706Torsion23_of_threeCard (h3 : S1705ThreeTorsionFCard) :
    PuncturedEllipticCurve.Torsion23Rational
      (S1667Punctured.baseChange S1687Field) :=
  S1705Torsion23_of_FCards S1706TwoTorsionFCard h3

#check S1706TwoTorsionFCard
#check S1706ThreeTorsionFCardMissing
#check S1706Torsion2Rational
#check S1706Torsion23_of_threeCard

end LeanFormal.IUT.XiFPaper.S1706FCardActual
end
