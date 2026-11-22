import tmp.sheaf.xif.paper.S1423ThetaInvertibleActual
import tmp.sheaf.xif.paper.S1424ThetaSectionActual

/-!
# S1484: actual curve divisor carrier and the theta line bundle section

## Context

S1423 constructed the actual line bundle

  s1423LineBundle S : CommRing.Pic (s1423Ring S)

from Mathlib fractional ideals / the ideal class group / the Picard group, and
identified it with the class of the actual puncture ideal module.  The next
source-theta item is thetaObjectATheta: a theta structure / global section on a
line bundle whose zero divisor is the geometric theta divisor.

The only divisor carrier previously used in this branch was the arithmetic
divisor

  s1401DivisorType S = (NumberField.InfinitePlace S.arithmetic.F -> Z).

That is an arithmetic divisor on the number field, not a divisor on the curve.
This file does not substitute it for a curve divisor.

## What is constructed (actual data)

1. The actual curve divisor carrier

     s1484CurveDivisor S := (s1423Model S).Point ->_0 Z,

   the finitely supported integer functions on the actual affine point group
   of the source Weierstrass model.  The point group contains the point at
   infinity (0) and every nonsingular affine point (some x y h).

2. The actual point divisor at the puncture, its support and its degree.

3. For an affine point P = (x, y), the point ideal I_P = XYIdeal W x (C y),
   the actual rank-one projective module I_P, its dual line bundle

     s1484ThetaLineBundleAt S h := Pic.mk R (Module.Dual R I_P),

   and the canonical global section

     s1484ThetaSectionAt S h := Submodule.subtype : I_P -> R

   (the section corresponding to the constant function 1 under the
   identification Dual(I_P) = I_P^{-1}).

4. The zero locus and zero divisor of this section.  The section vanishes at an
   affine point Q = (qx, qy) exactly when I_P is contained in I_Q; using
   maximality of both point ideals and injectivity of Point.toClass this is
   equivalent to Q = P.  Hence the zero divisor is the actual curve point
   divisor [P], of support {P} and degree one.  The zero is simple: I_P is not
   contained in I_P^2 (an idempotent finitely generated ideal in a domain is
   zero or the unit ideal).

5. The constructed theta line bundle is the dual of the S1423 line bundle:

     s1484ThetaLineBundleAt S h = (s1423LineBundleAt S (some x y h))^{-1}.

   Thus the theta line bundle is a genuine Picard-group element, not an
   arbitrary carrier.

6. The q_v^(j^2) family of S1424 is re-exported.  It is a family of nonzero
   real units, so its label-indexed divisor is zero; it supplies no zero
   coefficient.  This is why the unit family alone cannot be the zero divisor
   of a nonzero curve theta section.

## Exact first missing structure

For an affine puncture the line bundle, the global section and its actual curve
zero divisor [P] are constructed.  The source-theta item that is still missing
is the identification of this constructed curve divisor [P] with the paper's
geometric theta divisor (the q_v^(j^2) divisor) and the comparison of the theta
values.  There is no map from the signed labels to actual curve points and no
curve-level q_v^(j^2) divisor in the current source contract; the unit family
is not such a divisor.  This is recorded as the exact first missing structure,
not replaced by the arithmetic divisor.

If the puncture is the point at infinity, the affine coordinate ring cannot see
that point: the S1423 line bundle is trivial on the affine chart and the
constant section has no affine zeros.  The projective theta line bundle /
divisor at infinity is then part of the same missing structure; the file proves
the affine-chart statement and the triviality in this case.

No sorry, axiom, native_decide, True/PUnit gate or Nonempty gate is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace ABCBridge.S1484ThetaObjectActual

open CommRing Pic
open WeierstrassCurve.Affine
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open ABCBridge.SourceQlThetaPunctureIdeal
open ABCBridge.S1423ThetaInvertibleActual
open ABCBridge.SourceQlThetaLineBundleFromCurve
open ABCBridge.S1401ThetaLineBundleActual
open ABCBridge.S1424ThetaSectionActual

universe u
variable {l : PrimeGeFive} (S : SourceDefinition31Data.{u} l)

local notation "Rq" => s1423Ring S

/-! ## 1. The actual curve divisor carrier -/

/-- The actual curve divisor group: finitely supported integer functions on the
actual affine point group of the source Weierstrass model.  This is a curve
carrier; it is not the arithmetic divisor carrier on infinite places. -/
abbrev s1484CurveDivisor : Type u := (s1423Model S).Point →₀ ℤ

/-- The divisor of a single actual curve point with a given coefficient. -/
noncomputable def s1484PointDivisor (P : (s1423Model S).Point) (n : ℤ) : s1484CurveDivisor S :=
  Finsupp.single P n

/-- The total degree (sum of coefficients) of an actual curve divisor. -/
noncomputable def s1484DivisorDegree (D : s1484CurveDivisor S) : ℤ :=
  D.sum (fun _ n => n)

@[simp] theorem s1484DivisorDegree_zero :
    s1484DivisorDegree S (0 : s1484CurveDivisor S) = 0 := by
  simp [s1484DivisorDegree]

@[simp] theorem s1484DivisorDegree_single (P : (s1423Model S).Point) (n : ℤ) :
    s1484DivisorDegree S (s1484PointDivisor S P n) = n := by
  simp [s1484DivisorDegree, s1484PointDivisor]

theorem s1484DivisorDegree_add (D E : s1484CurveDivisor S) :
    s1484DivisorDegree S (D + E) =
      s1484DivisorDegree S D + s1484DivisorDegree S E := by
  simp [s1484DivisorDegree, Finsupp.sum_add_index']

theorem s1484DivisorDegree_neg (D : s1484CurveDivisor S) :
    s1484DivisorDegree S (-D) = -s1484DivisorDegree S D := by
  simp [s1484DivisorDegree, Finsupp.sum_neg_index]

/-- The actual curve divisor at the puncture, with coefficient one. -/
noncomputable def s1484PunctureDivisor : s1484CurveDivisor S :=
  s1484PointDivisor S (s1423Point S) 1

theorem s1484PunctureDivisor_apply_self :
    s1484PunctureDivisor S (s1423Point S) = 1 := by
  rw [s1484PunctureDivisor, s1484PointDivisor]
  exact Finsupp.single_eq_same

theorem s1484PunctureDivisor_support :
    (s1484PunctureDivisor S).support = {s1423Point S} := by
  rw [s1484PunctureDivisor, s1484PointDivisor]
  exact Finsupp.support_single (s1423Point S) (by norm_num : (1 : ℤ) ≠ 0)

theorem s1484PunctureDivisor_degree :
    s1484DivisorDegree S (s1484PunctureDivisor S) = 1 := by
  rw [s1484PunctureDivisor]
  exact s1484DivisorDegree_single S _ 1

theorem s1484PunctureDivisor_ne_zero :
    s1484PunctureDivisor S ≠ 0 := by
  intro hzero
  have hcoeff := s1484PunctureDivisor_apply_self S
  rw [hzero] at hcoeff
  exact one_ne_zero hcoeff.symm

/-- The curve divisor carrier is exactly the finsupp carrier on the actual
curve points. -/
theorem s1484CurveDivisor_carrier :
    s1484CurveDivisor S = ((s1423Model S).Point →₀ ℤ) := rfl

/-- The arithmetic divisor carrier is the function type on infinite places,
not a curve divisor carrier. -/
theorem s1484ArithmeticDivisor_carrier :
    s1401DivisorType S = (NumberField.InfinitePlace S.arithmetic.F → ℤ) :=
  s1423DivisorType_eq S

/-! ## 2. The point ideal, the dual theta line bundle and its section -/

/-- The actual point ideal module at an affine point. -/
noncomputable abbrev s1484PointIdealModule {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) : Type u :=
  ↥(CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y))

instance s1484PointIdealModule_invertible {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) :
    Module.Invertible Rq (s1484PointIdealModule S h) :=
  LeanFormal.IUT.AffinePunctureIdeal.pointIdeal_invertible (s1423Model S) h

/-- The theta line bundle module at an affine point: the dual of the point
ideal module, i.e. the module of the line bundle O(P). -/
noncomputable abbrev s1484ThetaModuleAt {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) : Type u :=
  Module.Dual (Rq) (s1484PointIdealModule S h)

instance s1484ThetaModuleAt_invertible {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) :
    Module.Invertible (Rq) (s1484ThetaModuleAt S h) := by
  letI : Module.Invertible (Rq) (s1484PointIdealModule S h) :=
    s1484PointIdealModule_invertible S h
  infer_instance

/-- The actual theta line bundle at an affine point, as a Picard-group element. -/
noncomputable def s1484ThetaLineBundleAt {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) : CommRing.Pic (Rq) :=
  Pic.mk (Rq) (s1484ThetaModuleAt S h)

/-- The canonical global section: the inclusion I_P -> R.  Under the
identification Dual(I_P) = I_P^{-1}, this is the section corresponding to the
constant function 1. -/
noncomputable def s1484ThetaSectionAt {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) : s1484ThetaModuleAt S h :=
  (CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y)).subtype

/-- The canonical theta section evaluated at an element of the point ideal is
the element itself (the inclusion I_P -> R). -/
@[simp] theorem s1484ThetaSectionAt_apply {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y)
    (a : s1484PointIdealModule S h) :
    (s1484ThetaSectionAt S h) a = (a : Rq) := rfl

/-- The section at an affine point Q vanishes exactly when the point ideal of P
is contained in the point ideal of Q. -/
def s1484ThetaSectionVanishesAt {x y : S.arithmetic.F}
    (_h : (s1423Model S).Nonsingular x y) (qx qy : S.arithmetic.F) : Prop :=
  CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y) ≤
    CoordinateRing.XYIdeal (s1423Model S) qx (Polynomial.C qy)

/-- The ideal-inclusion vanishing condition is equivalent to the statement
that every value of the canonical section lies in the point ideal of Q. -/
theorem s1484ThetaSection_values_mem_iff {x y qx qy : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) :
    s1484ThetaSectionVanishesAt S h qx qy ↔
      ∀ a : s1484PointIdealModule S h,
        (s1484ThetaSectionAt S h) a ∈
          CoordinateRing.XYIdeal (s1423Model S) qx (Polynomial.C qy) := by
  constructor
  · intro hv a
    exact hv a.2
  · intro hv a ha
    exact hv ⟨a, ha⟩

/-! ## 3. The point ideal is maximal and the zero locus is a single point -/

/-- The affine point ideal of a nonsingular point is maximal: its quotient is
the base field. -/
theorem s1484PointIdeal_isMaximal {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) :
    (CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y)).IsMaximal := by
  have hEq : Polynomial.eval x
      (Polynomial.eval (Polynomial.C y) (s1423Model S).polynomial) = 0 := h.1
  let q := CoordinateRing.quotientXYIdealEquiv (W' := (s1423Model S))
    (x := x) (y := Polynomial.C y) hEq
  refine Ideal.Quotient.maximal_of_isField _ ?_
  exact MulEquiv.isField (Field.toIsField S.arithmetic.F) q.toRingEquiv

/-- The affine point ideal is nonzero. -/
theorem s1484PointIdeal_ne_bot {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) :
    CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y) ≠ ⊥ := by
  intro hbot
  have hmem : CoordinateRing.XClass (s1423Model S) x ∈ (⊥ : Ideal (Rq)) := by
    rw [← hbot]
    exact Ideal.subset_span (by simp)
  exact CoordinateRing.XClass_ne_zero x (by simpa using hmem)

/-- The canonical theta section vanishes at an affine point Q exactly when
Q = P. -/
theorem s1484ThetaSectionVanishesAt_iff {x y qx qy : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) (hq : (s1423Model S).Nonsingular qx qy) :
    s1484ThetaSectionVanishesAt S h qx qy ↔ (qx = x ∧ qy = y) := by
  classical
  constructor
  · intro hle
    have hIPmax :
        (CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y)).IsMaximal :=
      s1484PointIdeal_isMaximal S h
    have hIQmax :
        (CoordinateRing.XYIdeal (s1423Model S) qx (Polynomial.C qy)).IsMaximal :=
      s1484PointIdeal_isMaximal S hq
    have hEq : CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y) =
        CoordinateRing.XYIdeal (s1423Model S) qx (Polynomial.C qy) :=
      Ideal.IsMaximal.eq_of_le hIPmax hIQmax.ne_top hle
    have hunits : CoordinateRing.XYIdeal' (W := (s1423Model S)) h =
        CoordinateRing.XYIdeal' (W := (s1423Model S)) hq := by
      ext
      rw [CoordinateRing.XYIdeal'_eq, CoordinateRing.XYIdeal'_eq, hEq]
    have hclasses : ClassGroup.mk (s1423Model S).FunctionField
          (CoordinateRing.XYIdeal' (W := (s1423Model S)) h) =
        ClassGroup.mk (s1423Model S).FunctionField
          (CoordinateRing.XYIdeal' (W := (s1423Model S)) hq) := by
      rw [hunits]
    have hpoint : (WeierstrassCurve.Affine.Point.some x y h : (s1423Model S).Point) =
        WeierstrassCurve.Affine.Point.some qx qy hq := by
      apply Point.toClass_injective
      rw [Point.toClass_some, Point.toClass_some]
      exact hclasses
    injection hpoint with hx hy
    exact ⟨hx.symm, hy.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact le_rfl

/-- The zero at P is simple: the point ideal is not contained in its square. -/
theorem s1484ThetaSection_simple_zero {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) :
    ¬ CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y) ≤
        (CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y)) ^ 2 := by
  intro hle
  let IP := CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y)
  have hIPmax : IP.IsMaximal := s1484PointIdeal_isMaximal S h
  have hIPne : IP ≠ ⊥ := s1484PointIdeal_ne_bot S h
  have hsq : IP ^ 2 ≤ IP := Ideal.pow_le_self (by norm_num : 2 ≠ 0)
  have hEq : IP = IP ^ 2 := le_antisymm hle hsq
  have hidem : IsIdempotentElem IP := by
    rw [IsIdempotentElem, ← pow_two]
    exact hEq.symm
  have hfg : IP.FG := Submodule.fg_span (Set.toFinite _)
  rcases (Ideal.isIdempotentElem_iff_eq_bot_or_top IP hfg).mp hidem with
    hbot | htop
  · exact hIPne hbot
  · exact hIPmax.ne_top htop

/-- The canonical theta section is nonzero. -/
theorem s1484ThetaSectionAt_ne_zero {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) :
    s1484ThetaSectionAt S h ≠ 0 := by
  intro hzero
  let I := CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y)
  let a : I := ⟨CoordinateRing.XClass (s1423Model S) x,
    Ideal.subset_span (by simp)⟩
  have ha : (s1484ThetaSectionAt S h) a = (a : Rq) := rfl
  have hzero_eval : (s1484ThetaSectionAt S h) a = 0 := by
    rw [hzero]
    rfl
  have hxzero : (a : Rq) = 0 := by
    rw [← ha, hzero_eval]
  exact CoordinateRing.XClass_ne_zero x (by simpa [a] using hxzero)

/-! ## 4. The actual curve zero divisor of the theta section -/

/-- The actual curve zero divisor of the canonical theta section at an affine
point: coefficient one at that point. -/
noncomputable def s1484ThetaZeroDivisorAt {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) : s1484CurveDivisor S :=
  s1484PointDivisor S (WeierstrassCurve.Affine.Point.some x y h) 1

@[simp] theorem s1484ThetaZeroDivisorAt_apply_self {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) :
    s1484ThetaZeroDivisorAt S h (WeierstrassCurve.Affine.Point.some x y h) = 1 := by
  rw [s1484ThetaZeroDivisorAt, s1484PointDivisor]
  exact Finsupp.single_eq_same

theorem s1484ThetaZeroDivisorAt_support {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) :
    (s1484ThetaZeroDivisorAt S h).support =
      {WeierstrassCurve.Affine.Point.some x y h} := by
  rw [s1484ThetaZeroDivisorAt, s1484PointDivisor]
  exact Finsupp.support_single (WeierstrassCurve.Affine.Point.some x y h)
    (by norm_num : (1 : ℤ) ≠ 0)

theorem s1484ThetaZeroDivisorAt_degree {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) :
    s1484DivisorDegree S (s1484ThetaZeroDivisorAt S h) = 1 := by
  rw [s1484ThetaZeroDivisorAt]
  exact s1484DivisorDegree_single S _ 1

theorem s1484ThetaZeroDivisorAt_ne_zero {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) :
    s1484ThetaZeroDivisorAt S h ≠ 0 := by
  intro hzero
  have hcoeff := s1484ThetaZeroDivisorAt_apply_self S h
  rw [hzero] at hcoeff
  exact one_ne_zero hcoeff.symm

/-- The zero locus of the canonical theta section is exactly the singleton
point P. -/
theorem s1484ThetaSection_zeroLocus {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) :
    {Q : (s1423Model S).Point |
      ∃ qx qy hq, Q = WeierstrassCurve.Affine.Point.some qx qy hq ∧
        s1484ThetaSectionVanishesAt S h qx qy} =
      {WeierstrassCurve.Affine.Point.some x y h} := by
  classical
  ext Q
  constructor
  · rintro ⟨qx, qy, hq, rfl, hv⟩
    have hqx := (s1484ThetaSectionVanishesAt_iff S h hq).mp hv
    rcases hqx with ⟨rfl, rfl⟩
    rfl
  · intro hQ
    rw [Set.mem_singleton_iff] at hQ
    subst hQ
    exact ⟨x, y, h, rfl,
      (s1484ThetaSectionVanishesAt_iff S h h).mpr ⟨rfl, rfl⟩⟩

/-! ## 5. The theta line bundle is the dual of the S1423 line bundle -/

/-- The constructed theta line bundle is the inverse of the S1423 line bundle
at the same affine point. -/
theorem s1484ThetaLineBundleAt_eq_inv_lineBundleAt {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) :
    s1484ThetaLineBundleAt S h =
      (s1423LineBundleAt S (WeierstrassCurve.Affine.Point.some x y h))⁻¹ := by
  classical
  rw [s1484ThetaLineBundleAt, s1423LineBundleAt, s1423PointClassAt,
    Point.toClass_some]
  change Pic.mk (Rq) (Module.Dual (Rq) (s1484PointIdealModule S h)) =
    (ClassGroup.equivPic (Rq)
      (ClassGroup.mk (s1423Model S).FunctionField
        (CoordinateRing.XYIdeal' (W := (s1423Model S)) h)))⁻¹
  letI : Module.Invertible (s1423Model S).CoordinateRing
      ↥(CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y)) :=
    LeanFormal.IUT.AffinePunctureIdeal.pointIdeal_invertible (s1423Model S) h
  rw [← s1423_pointIdeal_pic_eq_equivPic (W := (s1423Model S)) h]
  exact Pic.mk_dual (R := Rq) (M := s1484PointIdealModule S h)

/-! ## 6. The puncture case split and the exact first missing structure -/

/-- Every actual puncture is either the point at infinity or an affine
nonsingular point. -/
theorem s1484Puncture_zero_or_affine :
    s1423Point S = 0 ∨
      ∃ (x y : S.arithmetic.F) (h : (s1423Model S).Nonsingular x y),
        s1423Point S = WeierstrassCurve.Affine.Point.some x y h := by
  rcases s1423Point S with _ | ⟨x, y, h⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨x, y, h, rfl⟩

/-- Affine puncture: the theta line bundle is the dual of the S1423 line
bundle, and the canonical theta section has actual curve zero divisor [P] of
degree one. -/
theorem s1484Puncture_affine_thetaData {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y)
    (hP : s1423Point S = WeierstrassCurve.Affine.Point.some x y h) :
    s1484ThetaLineBundleAt S h = (s1423LineBundle S)⁻¹ ∧
      (s1484ThetaZeroDivisorAt S h).support = {s1423Point S} ∧
      s1484DivisorDegree S (s1484ThetaZeroDivisorAt S h) = 1 := by
  constructor
  · rw [s1484ThetaLineBundleAt_eq_inv_lineBundleAt S h]
    rw [s1423LineBundle, hP]
  · constructor
    · rw [s1484ThetaZeroDivisorAt_support, hP]
    · exact s1484ThetaZeroDivisorAt_degree S h

/-- Infinity puncture: the S1423 line bundle is trivial on the affine chart. -/
theorem s1484Puncture_infinity_trivial
    (hP : s1423Point S = 0) :
    s1423LineBundle S = 1 := by
  rw [s1423LineBundle, hP]
  exact s1423LineBundleAt_zero S

/-- The constant section of the trivial line bundle has no affine zero: the
point at infinity is invisible to the affine coordinate ring. -/
theorem s1484TrivialThetaSection_not_vanishes_at_affine {qx qy : S.arithmetic.F}
    (hq : (s1423Model S).Nonsingular qx qy) :
    (1 : Rq) ∉ CoordinateRing.XYIdeal (s1423Model S) qx (Polynomial.C qy) := by
  intro hmem
  exact (s1484PointIdeal_isMaximal S hq).ne_top (by
      rw [Ideal.eq_top_iff_one]
      exact hmem)

/-- The actual divisor at the point at infinity, of degree one.  It is a curve
divisor, but the affine constant section does not see it. -/
noncomputable def s1484InfinityDivisor : s1484CurveDivisor S :=
  s1484PointDivisor S 0 1

theorem s1484InfinityDivisor_degree :
    s1484DivisorDegree S (s1484InfinityDivisor S) = 1 := by
  rw [s1484InfinityDivisor]
  exact s1484DivisorDegree_single S _ 1

/-! ## 7. The q_v^(j^2) family and the exact missing identification -/

/-- The actual q_v^(j^2) unit family, re-exported from S1424. -/
noncomputable abbrev s1484ThetaValueFamily
    (t : LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaGenerator.AnalyticThetaCarrier) :
    LeanFormal.IUT.SignedLabel l.value → ℝˣ :=
  s1424ThetaValueFamily (l := l) t

/-- Each theta value is the corresponding power of the q-unit. -/
theorem s1484ThetaValueFamily_eq_qUnit_pow
    (t : LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaGenerator.AnalyticThetaCarrier)
    (j : LeanFormal.IUT.SignedLabel l.value) :
    s1484ThetaValueFamily (l := l) t j =
      LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaDivisor.thetaQUnit t ^
        (LeanFormal.IUT.gaussExponent j.1).toNat :=
  s1424ThetaValueFamily_eq_qUnit_pow (l := l) t j

/-- Every q_v^(j^2) value is a nonzero real unit. -/
theorem s1484ThetaValueFamily_ne_zero
    (t : LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaGenerator.AnalyticThetaCarrier)
    (j : LeanFormal.IUT.SignedLabel l.value) :
    ((s1484ThetaValueFamily (l := l) t j : ℝ)) ≠ 0 :=
  s1424ThetaValueFamily_ne_zero (l := l) t j

/-- The label-indexed q_v^(j^2) divisor of the actual unit family. -/
noncomputable abbrev s1484QJ2LabelDivisor :
    LeanFormal.IUT.SignedLabel l.value →₀ ℤ :=
  s1424QJ2Divisor (l := l)

/-- The label-indexed q_v^(j^2) divisor is zero: the unit family has no zero
coefficient. -/
theorem s1484QJ2LabelDivisor_eq_zero :
    s1484QJ2LabelDivisor (l := l) = 0 :=
  s1424QJ2Divisor_eq_zero (l := l)

/-- Its support is empty. -/
theorem s1484QJ2LabelDivisor_support_empty :
    (s1484QJ2LabelDivisor (l := l)).support = ∅ :=
  s1424QJ2Divisor_support_empty (l := l)

/-- The q_v^(j^2) unit family does not supply a nonzero curve divisor: its
label-indexed divisor is empty, while the actual theta curve divisor [P] is
nonzero of degree one. -/
theorem s1484QJ2LabelDivisor_ne_curveThetaDivisor {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) :
    (s1484QJ2LabelDivisor (l := l)).support = ∅
      ∧ (s1484ThetaZeroDivisorAt S h).support =
        {WeierstrassCurve.Affine.Point.some x y h}
      ∧ s1484ThetaZeroDivisorAt S h ≠ 0 :=
  ⟨s1484QJ2LabelDivisor_support_empty (l := l),
    s1484ThetaZeroDivisorAt_support S h,
    s1484ThetaZeroDivisorAt_ne_zero S h⟩

/-- Exact first missing structure after the actual curve divisor carrier and
the canonical theta section: a curve-level geometric theta divisor together
with the identification of the zero divisor of the theta section with that
divisor and with the q_v^(j^2) special values.  The line bundle, the global
section and its actual point zero divisor are constructed above; the missing
part is the geometric theta divisor on the curve, not the arithmetic divisor
on infinite places. -/
inductive s1484GeometricThetaMissingDatum : Type
  | curveThetaDivisor
  | zeroDivisorIdentification
  | thetaValueComparison
  deriving DecidableEq, Repr

/-- The ordered exact missing data. -/
def s1484GeometricThetaMissingData :
    List s1484GeometricThetaMissingDatum :=
  [ .curveThetaDivisor, .zeroDivisorIdentification, .thetaValueComparison ]

theorem s1484GeometricThetaMissingData_length :
    (s1484GeometricThetaMissingData).length = 3 := rfl

/-- The exact first missing structure: a curve-level geometric theta divisor.
It is a curve divisor, not the arithmetic divisor on infinite places. -/
def s1484FirstMissingStructure : s1484GeometricThetaMissingDatum :=
  .curveThetaDivisor

theorem s1484FirstMissingStructure_eq_curve :
    s1484FirstMissingStructure = .curveThetaDivisor := rfl

theorem s1484FirstMissingStructure_eq_head :
    (s1484GeometricThetaMissingData).head? = some s1484FirstMissingStructure := rfl

/-- The S1423 remaining source-theta list still starts with the theta object:
the line-bundle/section half of it is now constructed, but its geometric
divisor half is exactly the first missing curve-level datum. -/
theorem s1484ThetaObject_stillFirst :
    s1423RemainingThetaMissingData S =
      ABCBridge.SourceQlThetaLineBundleFromCurve.SourceThetaLineBundleMissingDatum.thetaObjectATheta ::
        [ ABCBridge.SourceQlThetaLineBundleFromCurve.SourceThetaLineBundleMissingDatum.geometricThetaDivisor,
          ABCBridge.SourceQlThetaLineBundleFromCurve.SourceThetaLineBundleMissingDatum.unitComparisonMqMTheta,
          ABCBridge.SourceQlThetaLineBundleFromCurve.SourceThetaLineBundleMissingDatum.muTwoLDeckRootAction,
          ABCBridge.SourceQlThetaLineBundleFromCurve.SourceThetaLineBundleMissingDatum.conjugateSynchronization ] :=
  rfl

/-- Combined exact statement: for an affine puncture the actual theta line
bundle, global section and curve zero divisor are constructed, while the
geometric theta divisor identification remains the first missing curve-level
structure and the q_v^(j^2) unit family is not a substitute. -/
theorem s1484ThetaObject_geometricPart_and_exactGap {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) :
    s1484ThetaLineBundleAt S h =
        (s1423LineBundleAt S (WeierstrassCurve.Affine.Point.some x y h))⁻¹
      ∧ s1484ThetaSectionAt S h ≠ 0
      ∧ (s1484ThetaZeroDivisorAt S h).support =
        {WeierstrassCurve.Affine.Point.some x y h}
      ∧ s1484DivisorDegree S (s1484ThetaZeroDivisorAt S h) = 1
      ∧ (∀ (qx qy : S.arithmetic.F)
          (hq : (s1423Model S).Nonsingular qx qy),
          s1484ThetaSectionVanishesAt S h qx qy ↔ (qx = x ∧ qy = y))
      ∧ (s1484QJ2LabelDivisor (l := l) = 0)
      ∧ s1484FirstMissingStructure = .curveThetaDivisor :=
  ⟨s1484ThetaLineBundleAt_eq_inv_lineBundleAt S h,
    s1484ThetaSectionAt_ne_zero S h,
    s1484ThetaZeroDivisorAt_support S h,
    s1484ThetaZeroDivisorAt_degree S h,
    fun qx qy hq => s1484ThetaSectionVanishesAt_iff S h hq,
    s1484QJ2LabelDivisor_eq_zero (l := l),
    rfl⟩

/-- The exact first missing source-theta field remains thetaObjectATheta; what
this file removes is its geometric line-bundle/section/curve-divisor part. -/
theorem s1484FirstMissingField_eq :
    s1423FirstMissingField =
      [ SourceThetaLineBundleMissingDatum.thetaObjectATheta ] :=
  rfl

end ABCBridge.S1484ThetaObjectActual

end