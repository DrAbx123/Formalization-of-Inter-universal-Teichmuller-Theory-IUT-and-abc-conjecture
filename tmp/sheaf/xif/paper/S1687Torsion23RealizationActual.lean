import tmp.sheaf.xif.paper.S1667AdmissibleCurveActual
import tmp.sheaf.xif.paper.S1637D5TorsionClauseActual
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.NumberTheory.NumberField.Basic

/-!
# S1687: actual construction of the S1667 2*3-torsion realization

The S1667 curve is

  E : y^2 = x^3 + (61/64) x^2 - (125/64) x.

Its 3-division polynomial is

  psi_3(x) = (1/256) (x - 25/16) (768 x^3 + 2176 x^2 + 400 x + 625).

The residual cubic has no rational root (proved in S1667).  The first
missing point of the paper realization is the actual number field and the
actual coordinates of the eight 3-torsion points.

This file constructs the actual number field carrier

  F = SplittingField (463856467968 X^6 + 3973952045056 X^4
                        + 1991485440000 X^2 + 6153500390625),

which is the splitting field of the explicit even polynomial H; a genuine
root y of H in F is the y-coordinate of a non-rational 3-torsion point.  It then proves, with no axiom and no sorry, that

  (A(y^2), y)

is a nonsingular 3-torsion point of E over F, where

  A(t) = -3145728/33958225 t^2 - 2876416/6237225 t - 14425/55442.

The construction is uniform in the root: every root r of the defining
polynomial gives the point (A(r^2), r).  The two rational points
(25/16, plus/minus 225/128) are also available, so the file constructs the whole
eight-point family.  The six roots are proved distinct.  The remaining
torsion input is the proof that the eight-point family exhausts all
3-torsion over the algebraic closure; that is the exact remaining input
for Torsion23Rational.  The split-multiplicative place above 5 is
constructed by lying-over and the base-change theorem of
ReductionBaseChange, conditional on the rational split-reduction proof.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1637D5TorsionClauseActual

/-! ## 1. The concrete defining polynomials -/

/-- The candidate minimal polynomial of a non-rational 3-torsion y-coordinate. -/
def S1687H : ℚ[X] :=
  C 463856467968 * X ^ 6 + C 3973952045056 * X ^ 4 +
    C 1991485440000 * X ^ 2 + C 6153500390625

/-- The formal derivative of S1687H. -/
def S1687H' : ℚ[X] :=
  C 2783138807808 * X ^ 5 + C 15895808180224 * X ^ 3 + C 3982970880000 * X

/-- The cubic whose roots are the squares of the roots of S1687H. -/
def S1687P : ℚ[X] :=
  C 463856467968 * X ^ 3 + C 3973952045056 * X ^ 2 +
    C 1991485440000 * X + C 6153500390625

/-- The residual cubic of the 3-division polynomial. -/
def S1687F : ℚ[X] :=
  C 768 * X ^ 3 + C 2176 * X ^ 2 + C 400 * X + C 625

/-- The Weierstrass cubic x^3 + (61/64)x^2 - (125/64)x. -/
def S1687G : ℚ[X] :=
  C 1 * X ^ 3 + C (61/64 : ℚ) * X ^ 2 - C (125/64 : ℚ) * X

/-- The x-coordinate as a polynomial function of t = y^2. -/
def S1687A : ℚ[X] :=
  C (-3145728/33958225 : ℚ) * X ^ 2 +
    C (-2876416/6237225 : ℚ) * X + C (-14425/55442 : ℚ)

/-- The quotient of F(A(t)) by P(t). -/
def S1687Q1 : ℚ[X] :=
  C (-(12524124635136 : ℚ)/9515710442487800081671875) * X ^ 3 +
    C (-(79751150567424 : ℚ)/9515710442487800081671875) * X ^ 2 +
    C ((83360885866496 : ℚ)/9515710442487800081671875) * X +
    C ((1012427556339675 : ℚ)/9515710442487800081671875)

/-- The quotient of G(A(t)) - t by P(t). -/
def S1687Q2 : ℚ[X] :=
  C (-(12524124635136 : ℚ)/7308065619830630462724000000) * X ^ 3 +
    C (-(79751150567424 : ℚ)/7308065619830630462724000000) * X ^ 2 +
    C (-(170840063183104 : ℚ)/7308065619830630462724000000) * X +
    C ((659223575628975 : ℚ)/7308065619830630462724000000)

/-! ## 2. The pointwise polynomial identities -/

/-- F(A(t)) = P(t) Q1(t). -/
theorem S1687F_eval_A {K : Type*} [Field K] [Algebra ℚ K] [CharZero K] (t : K) :
    aeval (aeval t S1687A) S1687F =
      (aeval t S1687P) * (aeval t S1687Q1) := by
  unfold S1687F S1687A S1687P S1687Q1
  simp only [aeval_add, aeval_mul, aeval_X, aeval_C, map_pow, map_ofNat]
  simp only [show ∀ q : ℚ, algebraMap ℚ K q = (q : K) from fun q => by
    rw [← map_ratCast (algebraMap ℚ K) q]; rfl]
  ring_nf

/-- G(A(t)) - t = P(t) Q2(t). -/
theorem S1687G_eval_A {K : Type*} [Field K] [Algebra ℚ K] [CharZero K] (t : K) :
    aeval (aeval t S1687A) S1687G - t =
      (aeval t S1687P) * (aeval t S1687Q2) := by
  unfold S1687G S1687A S1687P S1687Q2
  simp only [aeval_add, aeval_sub, aeval_mul, aeval_X, aeval_C, map_pow, map_ofNat]
  simp only [show ∀ q : ℚ, algebraMap ℚ K q = (q : K) from fun q => by
    rw [← map_ratCast (algebraMap ℚ K) q]; rfl]
  ring_nf

/-- H(t) = P(t^2). -/
theorem S1687H_eval_eq {K : Type*} [Field K] [Algebra ℚ K] [CharZero K] (t : K) :
    aeval t S1687H = aeval (t ^ 2) S1687P := by
  unfold S1687H S1687P
  simp only [aeval_add, aeval_mul, aeval_X, aeval_C, map_pow, map_ofNat]
  ring_nf



/-! ## 3. The actual number field and the first actual 3-torsion point -/

/-- The actual number field carrier: the splitting field of S1687H. -/
abbrev S1687Field : Type := Polynomial.SplittingField S1687H

local instance S1687FieldDecEq : DecidableEq S1687Field := Classical.decEq _

instance : NumberField S1687Field where
  to_charZero := inferInstance
  to_finiteDimensional := by
    letI : IsSplittingField ℚ S1687Field S1687H :=
      Polynomial.IsSplittingField.splittingField S1687H
    exact Polynomial.IsSplittingField.finiteDimensional S1687Field S1687H

theorem S1687H_natDegree : S1687H.natDegree = 6 := by
  unfold S1687H
  compute_degree!

theorem S1687H_ne_zero : S1687H ≠ 0 := by
  intro h
  have hd := S1687H_natDegree
  rw [h, Polynomial.natDegree_zero] at hd
  norm_num at hd

theorem S1687H_degree : S1687H.degree = (6 : WithBot ℕ) := by
  rw [Polynomial.degree_eq_natDegree S1687H_ne_zero, S1687H_natDegree]
  norm_num

theorem S1687H_degree_ne_zero : S1687H.degree ≠ 0 := by
  rw [S1687H_degree]
  norm_num

theorem S1687H_map_ne_zero :
    S1687H.map (algebraMap ℚ S1687Field) ≠ 0 := by
  intro h
  exact S1687H_ne_zero
    ((Polynomial.map_eq_zero_iff (algebraMap ℚ S1687Field).injective).mp h)

theorem S1687H_map_natDegree :
    (S1687H.map (algebraMap ℚ S1687Field)).natDegree = 6 := by
  rw [Polynomial.natDegree_map_eq_of_injective
    (algebraMap ℚ S1687Field).injective, S1687H_natDegree]

theorem S1687H_map_degree :
    (S1687H.map (algebraMap ℚ S1687Field)).degree = (6 : WithBot ℕ) := by
  rw [Polynomial.degree_eq_natDegree S1687H_map_ne_zero, S1687H_map_natDegree]
  norm_num

theorem S1687H_map_degree_ne_zero :
    (S1687H.map (algebraMap ℚ S1687Field)).degree ≠ 0 := by
  rw [S1687H_map_degree]
  norm_num

/-- A genuine root of S1687H in the actual splitting field. -/
noncomputable def S1687Y : S1687Field :=
  Polynomial.rootOfSplits (Polynomial.SplittingField.splits S1687H) S1687H_map_degree_ne_zero

theorem S1687Y_root_map :
    (S1687H.map (algebraMap ℚ S1687Field)).eval S1687Y = 0 :=
  Polynomial.eval_rootOfSplits _ _

theorem S1687Y_root : aeval S1687Y S1687H = 0 := by
  simpa [Polynomial.aeval_def, Polynomial.eval_map] using S1687Y_root_map

theorem S1687H_eval_zero : aeval (0 : S1687Field) S1687H = 6153500390625 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero]
  rw [show S1687H.coeff 0 = 6153500390625 by simp [S1687H]]
  norm_num

theorem S1687Y_ne_zero : S1687Y ≠ 0 := by
  intro hy
  have h0 : aeval (0 : S1687Field) S1687H = 0 := by simpa [hy] using S1687Y_root
  rw [S1687H_eval_zero] at h0
  norm_num at h0

/-- The x-coordinate attached to a y-coordinate. -/
def S1687Alpha (y : S1687Field) : S1687Field :=
  aeval (y ^ 2) S1687A

theorem S1687Y_sq_root : aeval (S1687Y ^ 2) S1687P = 0 := by
  rw [← S1687H_eval_eq]
  exact S1687Y_root

theorem S1687Y_alpha_f : aeval (S1687Alpha S1687Y) S1687F = 0 := by
  unfold S1687Alpha
  rw [S1687F_eval_A, S1687Y_sq_root, zero_mul]

theorem S1687Y_alpha_g : aeval (S1687Alpha S1687Y) S1687G = S1687Y ^ 2 := by
  unfold S1687Alpha
  have h := S1687G_eval_A (S1687Y ^ 2)
  rw [S1687Y_sq_root, zero_mul] at h
  exact sub_eq_zero.mp h



/-! ## 4. The base-changed curve and the point -/

/-- The base change of the S1667 curve to the actual field. -/
abbrev S1687CurveF : WeierstrassCurve S1687Field :=
  S1667Curve.baseChange S1687Field

/-- The affine base-changed curve. -/
abbrev S1687AffineF : WeierstrassCurve.Affine S1687Field :=
  S1687CurveF.toAffine

theorem S1687Y_alpha_equation :
    S1687AffineF.Equation (S1687Alpha S1687Y) S1687Y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  rw [← S1687Y_alpha_g]
  unfold S1687G S1687AffineF S1687CurveF S1667Curve
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, WeierstrassCurve.toAffine]
  simp only [show ∀ q : ℚ, algebraMap ℚ S1687Field q = (q : S1687Field) from fun q => by
    rw [← map_ratCast (algebraMap ℚ S1687Field) q]; rfl]
  norm_num
  ring



/-- The 3-division polynomial identity, evaluated in any characteristic-zero
algebra over the rationals. -/
theorem S1687_Ψ3_eval_A {K : Type*} [Field K] [Algebra ℚ K] [CharZero K]
    (x : K) :
    aeval x S1667Curve.Ψ₃ =
      (1/256 : K) * (x - 25/16) * aeval x S1687F := by
  unfold S1687F S1667Curve
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  simp only [aeval_add, aeval_mul, aeval_sub, aeval_X, aeval_C, map_pow, map_ofNat]
  simp only [show ∀ q : ℚ, algebraMap ℚ K q = (q : K) from fun q => by
    rw [← map_ratCast (algebraMap ℚ K) q]; rfl]
  ring_nf

/-- The base-changed division polynomial evaluates as the rational one. -/
theorem S1687_ΨSq_eval_baseChange (n : ℤ) (x : S1687Field) :
    (S1687CurveF.ΨSq n).eval x = aeval x (S1667Curve.ΨSq n) := by
  change ((S1667Curve.map (algebraMap ℚ S1687Field)).ΨSq n).eval x =
    aeval x (S1667Curve.ΨSq n)
  rw [WeierstrassCurve.map_ΨSq, Polynomial.eval_map, Polynomial.aeval_def]



theorem S1687Y_alpha_psi3 :
    aeval (S1687Alpha S1687Y) S1667Curve.Ψ₃ = 0 := by
  rw [S1687_Ψ3_eval_A]
  rw [S1687Y_alpha_f]
  ring

theorem S1687Y_alpha_psiSq :
    aeval (S1687Alpha S1687Y) (S1667Curve.ΨSq 3) = 0 := by
  rw [WeierstrassCurve.ΨSq_three, map_pow, S1687Y_alpha_psi3]
  ring

theorem S1687Y_alpha_psiSq_base :
    (S1687CurveF.ΨSq 3).eval (S1687Alpha S1687Y) = 0 := by
  rw [S1687_ΨSq_eval_baseChange]
  exact S1687Y_alpha_psiSq

theorem S1687Y_alpha_nonsingular :
    S1687AffineF.Nonsingular (S1687Alpha S1687Y) S1687Y := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact S1687Y_alpha_equation
  · right
    unfold S1687AffineF S1687CurveF S1667Curve
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, WeierstrassCurve.toAffine]
    simp only [show ∀ q : ℚ, algebraMap ℚ S1687Field q = (q : S1687Field) from fun q => by
      rw [← map_ratCast (algebraMap ℚ S1687Field) q]; rfl]
    norm_num
    intro h
    have h2 : (2 : S1687Field) * S1687Y = 0 := by
      linear_combination h
    exact S1687Y_ne_zero ((mul_eq_zero.mp h2).resolve_left (by norm_num))

/-- The actual non-rational 3-torsion point in the actual number field. -/
def S1687YPoint : S1687AffineF.Point :=
  Affine.Point.some (W' := S1687AffineF)
    (S1687Alpha S1687Y) S1687Y S1687Y_alpha_nonsingular

theorem S1687YPoint_three : (3 : ℤ) • S1687YPoint = 0 := by
  classical
  have hJ : (3 : ℤ) • Jacobian.Point.fromAffine S1687YPoint = 0 :=
    (s1637EvalPsiSqEqZeroIffZsmul S1687CurveF S1687Y_alpha_nonsingular 3).mp
      S1687Y_alpha_psiSq_base
  exact (s1637ZsmulFromAffine S1687CurveF).mp hJ



/-! ## 5. The six-point family over the roots of the defining polynomial -/

theorem S1687Root_ne_zero (r : S1687Field) (hr : aeval r S1687H = 0) : r ≠ 0 := by
  intro h
  have h0 : aeval (0 : S1687Field) S1687H = 0 := by simpa [h] using hr
  rw [S1687H_eval_zero] at h0
  norm_num at h0

theorem S1687Root_sq_root (r : S1687Field) (hr : aeval r S1687H = 0) :
    aeval (r ^ 2) S1687P = 0 := by
  rw [← S1687H_eval_eq]
  exact hr

theorem S1687Root_alpha_f (r : S1687Field) (hr : aeval r S1687H = 0) :
    aeval (S1687Alpha r) S1687F = 0 := by
  unfold S1687Alpha
  rw [S1687F_eval_A, S1687Root_sq_root r hr, zero_mul]

theorem S1687Root_alpha_g (r : S1687Field) (hr : aeval r S1687H = 0) :
    aeval (S1687Alpha r) S1687G = r ^ 2 := by
  unfold S1687Alpha
  have h := S1687G_eval_A (r ^ 2)
  rw [S1687Root_sq_root r hr, zero_mul] at h
  exact sub_eq_zero.mp h

theorem S1687Root_equation (r : S1687Field) (hr : aeval r S1687H = 0) :
    S1687AffineF.Equation (S1687Alpha r) r := by
  rw [WeierstrassCurve.Affine.equation_iff]
  rw [← S1687Root_alpha_g r hr]
  unfold S1687G S1687AffineF S1687CurveF S1667Curve
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, WeierstrassCurve.toAffine]
  simp only [show ∀ q : ℚ, algebraMap ℚ S1687Field q = (q : S1687Field) from fun q => by
    rw [← map_ratCast (algebraMap ℚ S1687Field) q]; rfl]
  norm_num
  ring

theorem S1687Root_nonsingular (r : S1687Field) (hr : aeval r S1687H = 0) :
    S1687AffineF.Nonsingular (S1687Alpha r) r := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact S1687Root_equation r hr
  · right
    unfold S1687AffineF S1687CurveF S1667Curve
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, WeierstrassCurve.toAffine]
    simp only [show ∀ q : ℚ, algebraMap ℚ S1687Field q = (q : S1687Field) from fun q => by
      rw [← map_ratCast (algebraMap ℚ S1687Field) q]; rfl]
    norm_num
    intro h
    have h2 : (2 : S1687Field) * r = 0 := by
      linear_combination h
    exact S1687Root_ne_zero r hr ((mul_eq_zero.mp h2).resolve_left (by norm_num))

/-- The 3-torsion point attached to any root of the defining polynomial. -/
def S1687RootPoint (r : S1687Field) (hr : aeval r S1687H = 0) :
    S1687AffineF.Point :=
  Affine.Point.some (W' := S1687AffineF) (S1687Alpha r) r
    (S1687Root_nonsingular r hr)

/-- The explicit coordinates of a root point. -/
@[simp] theorem S1687RootPoint_coords (r : S1687Field) (hr : aeval r S1687H = 0) :
    S1687RootPoint r hr =
      Affine.Point.some (W' := S1687AffineF) (S1687Alpha r) r
        (S1687Root_nonsingular r hr) := rfl

theorem S1687RootPoint_three (r : S1687Field) (hr : aeval r S1687H = 0) :
    (3 : ℤ) • S1687RootPoint r hr = 0 := by
  classical
  have hpsi3 : aeval (S1687Alpha r) S1667Curve.Ψ₃ = 0 := by
    rw [S1687_Ψ3_eval_A]
    rw [S1687Root_alpha_f r hr]
    ring
  have hpsiSq : aeval (S1687Alpha r) (S1667Curve.ΨSq 3) = 0 := by
    rw [WeierstrassCurve.ΨSq_three, map_pow, hpsi3]
    ring
  have hpsiSqBase : (S1687CurveF.ΨSq 3).eval (S1687Alpha r) = 0 := by
    rw [S1687_ΨSq_eval_baseChange]
    exact hpsiSq
  have hJ : (3 : ℤ) • Jacobian.Point.fromAffine (S1687RootPoint r hr) = 0 :=
    (s1637EvalPsiSqEqZeroIffZsmul S1687CurveF
      (S1687Root_nonsingular r hr) 3).mp hpsiSqBase
  exact (s1637ZsmulFromAffine S1687CurveF).mp hJ

/-- The set of the six non-rational 3-torsion points. -/
def S1687RootPointSet : Set S1687AffineF.Point :=
  { P | ∃ (r : S1687Field) (hr : aeval r S1687H = 0), P = S1687RootPoint r hr }

theorem S1687RootPointSet_three {P : S1687AffineF.Point}
    (hP : P ∈ S1687RootPointSet) : (3 : ℤ) • P = 0 := by
  rcases hP with ⟨r, hr, rfl⟩
  exact S1687RootPoint_three r hr



/-! ## 6. The two rational points and the eight-point candidate set -/

theorem S1687RationalP_nonsingular :
    S1687AffineF.Nonsingular
      (algebraMap ℚ S1687Field (25/16)) (algebraMap ℚ S1687Field (225/128)) := by
  change (S1667Curve.toAffine.map (algebraMap ℚ S1687Field)).Nonsingular
    (algebraMap ℚ S1687Field (25/16)) (algebraMap ℚ S1687Field (225/128))
  rw [WeierstrassCurve.Affine.map_nonsingular
    (W := S1667Curve.toAffine) (f := algebraMap ℚ S1687Field)
    (algebraMap ℚ S1687Field).injective]
  exact S1667_nonsingular_P

/-- The base change of the rational 3-torsion point P = (25/16, 225/128). -/
def S1687RationalP : S1687AffineF.Point :=
  Affine.Point.some (W' := S1687AffineF)
    (algebraMap ℚ S1687Field (25/16)) (algebraMap ℚ S1687Field (225/128))
    S1687RationalP_nonsingular

/-- The explicit coordinates of the rational point P. -/
@[simp] theorem S1687RationalP_coords :
    S1687RationalP =
      Affine.Point.some (W' := S1687AffineF)
        (algebraMap ℚ S1687Field (25/16)) (algebraMap ℚ S1687Field (225/128))
        S1687RationalP_nonsingular := rfl

theorem S1687RationalP_psi3 :
    aeval (algebraMap ℚ S1687Field (25/16)) S1667Curve.Ψ₃ = 0 := by
  rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, S1667_Ψ₃_eval_P, map_zero]

theorem S1687RationalP_psiSq :
    aeval (algebraMap ℚ S1687Field (25/16)) (S1667Curve.ΨSq 3) = 0 := by
  rw [WeierstrassCurve.ΨSq_three, map_pow, S1687RationalP_psi3]
  ring

theorem S1687RationalP_psiSq_base :
    (S1687CurveF.ΨSq 3).eval (algebraMap ℚ S1687Field (25/16)) = 0 := by
  rw [S1687_ΨSq_eval_baseChange]
  exact S1687RationalP_psiSq

theorem S1687RationalP_three : (3 : ℤ) • S1687RationalP = 0 := by
  classical
  have hJ : (3 : ℤ) • Jacobian.Point.fromAffine S1687RationalP = 0 :=
    (s1637EvalPsiSqEqZeroIffZsmul S1687CurveF
      S1687RationalP_nonsingular 3).mp S1687RationalP_psiSq_base
  exact (s1637ZsmulFromAffine S1687CurveF).mp hJ

/-- The eight-point candidate set: six root points plus the two rational points. -/
def S1687EightPointSet : Set S1687AffineF.Point :=
  S1687RootPointSet ∪ {S1687RationalP, -S1687RationalP}

theorem S1687EightPointSet_three {P : S1687AffineF.Point}
    (hP : P ∈ S1687EightPointSet) : (3 : ℤ) • P = 0 := by
  rcases hP with hP | hP
  · exact S1687RootPointSet_three hP
  · rcases hP with rfl | rfl
    · exact S1687RationalP_three
    · rw [zsmul_neg, S1687RationalP_three, neg_zero]



/-! ## 7. Separability of the defining polynomial and distinctness of the roots -/

/-- A Bezout coefficient for the derivative certificate. -/
def S1687CertA : ℚ[X] :=
  C (-82812438839296/8254503789426745701416015625 : ℚ) * X ^ 4 +
    C (-404422570115072/13645200141705436771728515625 : ℚ) * X ^ 2 +
    C (1/6153500390625 : ℚ)

/-- The second Bezout coefficient for the derivative certificate. -/
def S1687CertB : ℚ[X] :=
  C (41406219419648/24763511368280237104248046875 : ℚ) * X ^ 5 +
    C (132559251488768/13645200141705436771728515625 : ℚ) * X ^ 3 +
    C (-19117874179/539069635227869107031250 : ℚ) * X

theorem S1687H_derivative : derivative S1687H = S1687H' := by
  simp only [S1687H, S1687H', derivative_add, derivative_mul, derivative_pow,
    derivative_C, derivative_X]
  norm_num
  simp only [← mul_assoc, ← C_mul]
  norm_num

/-- The Bezout identity, evaluated in any characteristic-zero field. -/
theorem S1687Bezout_eval {K : Type*} [Field K] [Algebra ℚ K] [CharZero K]
    (x : K) :
    aeval x S1687CertA * aeval x S1687H +
      aeval x S1687CertB * aeval x S1687H' = 1 := by
  unfold S1687CertA S1687CertB S1687H S1687H'
  simp only [aeval_add, aeval_mul, aeval_X, aeval_C, map_pow, map_ofNat]
  simp only [show ∀ q : ℚ, algebraMap ℚ K q = (q : K) from fun q => by
    rw [← map_ratCast (algebraMap ℚ K) q]; rfl]
  ring_nf

/-- The polynomial Bezout identity. -/
theorem S1687Bezout_poly :
    S1687CertA * S1687H + S1687CertB * S1687H' = 1 := by
  have h := S1687Bezout_eval (K := RatFunc ℚ) (RatFunc.X : RatFunc ℚ)
  have hX : (IsScalarTower.toAlgHom ℚ ℚ[X] (RatFunc ℚ)) X = RatFunc.X := by
    change algebraMap ℚ[X] (RatFunc ℚ) X = RatFunc.X
    exact RatFunc.algebraMap_X
  have hmap : ∀ p : ℚ[X],
      Polynomial.eval₂ (algebraMap ℚ (RatFunc ℚ)) (RatFunc.X) p =
        algebraMap ℚ[X] (RatFunc ℚ) p := by
    intro p
    rw [← hX,
      Polynomial.eval₂_algebraMap_X p
        (IsScalarTower.toAlgHom ℚ ℚ[X] (RatFunc ℚ))]
    rfl
  apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  simpa [Polynomial.aeval_def, hmap] using h

/-- The defining polynomial is separable. -/
theorem S1687H_separable : S1687H.Separable := by
  rw [separable_def']
  refine ⟨S1687CertA, S1687CertB, ?_⟩
  rw [S1687H_derivative]
  exact S1687Bezout_poly

/-- The six roots are distinct: the root set of the defining polynomial in the
actual splitting field has exactly six elements. -/
theorem S1687SixRootsDistinct :
    Nat.card (S1687H.rootSet S1687Field) = 6 := by
  have h := Polynomial.card_rootSet_eq_natDegree (K := S1687Field)
    S1687H_separable (Polynomial.SplittingField.splits S1687H)
  rw [S1687H_natDegree] at h
  exact (Fintype.card_eq_nat_card (α := S1687H.rootSet S1687Field)).symm.trans h

/-! ## 8. The exact missing realization inputs -/

/-- The literal paper condition (b) over the actual field.  This is the
torsion-side missing input: the eight-point family has been constructed, but
its exhaustiveness over the algebraic closure is not proved here. -/
def S1687Torsion23Missing : Prop :=
  PuncturedEllipticCurve.Torsion23Rational (S1667Punctured.baseChange S1687Field)

/-- The rational split-multiplicative reduction at 5.  This is the
reduction-side missing input, separated from the transport. -/
def S1687RationalSplitAtFive : Prop :=
  S1667Punctured.HasSplitMultiplicativeReductionAt concreteFivePlace

/-- The exact first missing package: the torsion condition and the rational
split reduction. -/
def S1687ExactFirstMissing : Prop :=
  S1687Torsion23Missing ∧ S1687RationalSplitAtFive

/-- The actual place of the number field above the rational place 5. -/
noncomputable def S1687PlaceAboveFive : NumberField.FinitePlace S1687Field :=
  Classical.choose
    (NumberFieldFinitePlace.comap_surjective
      (k := ℚ) (K := S1687Field) concreteFivePlace)

theorem S1687PlaceAboveFive_comap :
    NumberFieldFinitePlace.comap (k := ℚ) S1687PlaceAboveFive = concreteFivePlace :=
  Classical.choose_spec
    (NumberFieldFinitePlace.comap_surjective
      (k := ℚ) (K := S1687Field) concreteFivePlace)

/-- Split multiplicative reduction at the rational place 5 transports to the
actual place above 5.  This is the precise reduction-side transport. -/
theorem S1687Split_of_rational (h : S1687RationalSplitAtFive) :
    (S1667Punctured.baseChange S1687Field).HasSplitMultiplicativeReductionAt
      S1687PlaceAboveFive := by
  apply PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_baseChange
  rw [S1687PlaceAboveFive_comap]
  exact h

/-- Conditional realization data: an actual place of the actual field with
the two missing inputs supplied. -/
structure S1687RealizationData where
  place : NumberField.FinitePlace S1687Field
  odd_residueCharacteristic : Odd (NumberFieldFinitePlace.residueCharacteristic place)
  torsion23 : S1687Torsion23Missing
  splitMultiplicative :
    (S1667Punctured.baseChange S1687Field).HasSplitMultiplicativeReductionAt place

/-- The conditional data constructs the literal S1667 realization. -/
theorem S1687Admissible_of_data (D : S1687RealizationData) : S1667Admissible :=
  LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual.S1667Admissible_of_torsion23
    S1687Field D.place D.odd_residueCharacteristic D.torsion23 D.splitMultiplicative

/-- The exact missing package plus the two concrete place properties constructs
the realization. -/
theorem S1687Admissible_of_missing
    (h : S1687ExactFirstMissing)
    (place : NumberField.FinitePlace S1687Field)
    (hodd : Odd (NumberFieldFinitePlace.residueCharacteristic place))
    (hsplit : (S1667Punctured.baseChange S1687Field).HasSplitMultiplicativeReductionAt place) :
    S1667Admissible :=
  LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual.S1667Admissible_of_torsion23
    S1687Field place hodd h.1 hsplit



/-! ## 9. The precise first missing torsion sub-constructions -/

/-- Every F-rational 3-torsion point is one of the eight constructed points. -/
def S1687ThreeTorsionOverFClassified : Prop :=
  ∀ P : S1687AffineF.Point, (3 : ℤ) • P = 0 → P ∈ S1687EightPointSet

/-- The precise first missing torsion package: the F-rational 3-torsion
classification.  Distinctness of the six roots is now proved above as
S1687SixRootsDistinct. -/
def S1687FirstMissingTorsion : Prop :=
  S1687ThreeTorsionOverFClassified

/-- The literal closure statement, definitionally. -/
theorem S1687Torsion23Missing_eq :
    S1687Torsion23Missing =
      PuncturedEllipticCurve.Torsion23Rational
        (S1667Punctured.baseChange S1687Field) := rfl

/-- The split-reduction missing statement, definitionally. -/
theorem S1687RationalSplitAtFive_eq :
    S1687RationalSplitAtFive =
      S1667Punctured.HasSplitMultiplicativeReductionAt concreteFivePlace := rfl

/-! ## 10. Axiom footprint -/

#print axioms S1687F_eval_A
#print axioms S1687G_eval_A
#print axioms S1687H_eval_eq
#print axioms S1687Y_root
#print axioms S1687H_separable
#print axioms S1687SixRootsDistinct
#print axioms S1687YPoint_three
#print axioms S1687RootPoint_three
#print axioms S1687EightPointSet_three
#print axioms S1687PlaceAboveFive_comap
#print axioms S1687Split_of_rational
#print axioms S1687Admissible_of_data

end LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual