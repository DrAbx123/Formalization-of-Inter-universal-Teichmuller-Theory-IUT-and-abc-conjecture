/-
# S1553: actual source-curve theta on the S1423 line bundle

## Context

S1423 constructs the actual Picard line bundle

  s1423LineBundle S : CommRing.Pic (s1423Ring S)

from the actual puncture ideal module of the source Weierstrass model, and
identifies it with the class of that module (s1423ModuleClass_eq_lineBundle).
S1424 constructs the analytic theta section and the arithmetic/label q_v^(j^2)
family; it explicitly does not construct a source-curve theta section.
S1484 attempted the curve-level construction but currently does not compile
(its local notation for the Weierstrass model is ill-formed), so its
declarations are not used here.

## What this file constructs (actual data, no gate)

1. The actual curve divisor carrier

     s1553CurveDivisor S := (s1423Model S).Point ->_0 Z,

   the finitely supported integer functions on the actual affine point group
   of the source Weierstrass model, with point divisors, an additive degree
   homomorphism and its basic laws.

2. The actual global section of the S1423 line bundle:

   * for an affine puncture P = (x, y), the section X - x of the actual
     puncture ideal module s1423Module S (an element of the actual line
     bundle module), nonzero by XClass_ne_zero;
   * for the puncture at infinity, the section 1 of the unit ideal module.

3. The zero divisor of that section:

   * affine P: the zero locus is exactly {P, -P}, and the curve zero divisor
     is [P] + [-P], of degree 2;
   * infinity: the affine zero locus is empty and the zero divisor is 0.

4. The actual source-curve theta line bundle and its canonical theta section:

     s1553ThetaModule S := Module.Dual (s1423Ring S) (s1423Module S),
     s1553ThetaSection S := the inclusion s1423Module S -> s1423Ring S,
     s1553ThetaLineBundle S := Pic.mk (s1423Ring S) (s1553ThetaModule S),

   and the exact theorem

     s1553ThetaLineBundle S = (s1423LineBundle S)^(-1).

   The canonical theta section is the inclusion of the puncture ideal; it is
   nonzero.  At an affine puncture P its zero locus is exactly {P} and its
   curve zero divisor is [P], of degree 1.  At infinity its affine zero locus
   is empty (the point at infinity is invisible to the affine chart).

5. The q_v^(j^2) weighted curve divisor candidate: for a map from the signed
   labels to actual curve points, the divisor with coefficient j^2 at the
   image of j.  Its degree is the sum of the j^2 weights, which is at least 4
   (the label 2 contributes 4).  Consequently:

   * no such weighted divisor can be the actual theta divisor [P] (degree 1);
   * no such weighted divisor can be the S1423 section divisor [P] + [-P]
     (degree 2);

   and the corresponding naive q_j2 realization types are empty.

## Exact first missing geometric object

The actual theta line bundle, its canonical global section, and the actual
curve zero divisor [P] are constructed above.  The exact first missing
geometric object is a curve-level geometric theta divisor together with its
comparison with the q_v^(j^2) family: the source contract supplies neither a
geometric theta divisor on the source curve nor a map from the analytic theta
carrier/labels to curve points.  The naive realization of q_v^(j^2) as a
weighted point divisor is *impossible* (empty by the degree obstruction above),
so the missing object is a genuinely different geometric theta divisor, not
that weighted divisor.  The analytic theta section of S1424 has empty zero
divisor and is not substituted for a source-curve theta section here.

No sorry, admit, axiom, native_decide, True/PUnit gate or Nonempty gate is
used.
-/

import tmp.sheaf.xif.paper.S1423ThetaInvertibleActual
import tmp.sheaf.xif.paper.S1424ThetaSectionActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace ABCBridge.S1553SourceCurveThetaActual

open CommRing Pic
open WeierstrassCurve.Affine
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open ABCBridge.SourceQlThetaPunctureIdeal
open ABCBridge.S1423ThetaInvertibleActual
open ABCBridge.S1424ThetaSectionActual
open scoped BigOperators

universe u
variable {l : PrimeGeFive} (S : SourceDefinition31Data.{u} l)

attribute [local instance] Classical.decEq

/-! ## 1. The actual curve divisor carrier -/

/-- The actual curve divisor group: finitely supported integer functions on the
actual affine point group of the source Weierstrass model.  This is a curve
carrier, not the arithmetic divisor on infinite places. -/
abbrev s1553CurveDivisor : Type u := (s1423Model S).Point →₀ ℤ

/-- The divisor of a single actual curve point with a given coefficient. -/
noncomputable def s1553PointDivisor (P : (s1423Model S).Point) (n : ℤ) :
    s1553CurveDivisor S :=
  Finsupp.single P n

/-- The additive degree homomorphism on actual curve divisors. -/
noncomputable def s1553DegreeHom : s1553CurveDivisor S →+ ℤ :=
  Finsupp.liftAddHom (α := (s1423Model S).Point) (M := ℤ) (N := ℤ)
    (fun _ => AddMonoidHom.id ℤ)

/-- The total degree (sum of coefficients) of an actual curve divisor. -/
noncomputable def s1553DivisorDegree (D : s1553CurveDivisor S) : ℤ :=
  s1553DegreeHom S D

@[simp] theorem s1553DivisorDegree_zero :
    s1553DivisorDegree S (0 : s1553CurveDivisor S) = 0 :=
  map_zero _

@[simp] theorem s1553DivisorDegree_single (P : (s1423Model S).Point) (n : ℤ) :
    s1553DivisorDegree S (s1553PointDivisor S P n) = n := by
  simp [s1553DivisorDegree, s1553DegreeHom, s1553PointDivisor]

theorem s1553DegreeHom_single (P : (s1423Model S).Point) (n : ℤ) :
    s1553DegreeHom S (s1553PointDivisor S P n) = n := by
  simpa [s1553DivisorDegree] using s1553DivisorDegree_single S P n

theorem s1553DivisorDegree_add (D E : s1553CurveDivisor S) :
    s1553DivisorDegree S (D + E) =
      s1553DivisorDegree S D + s1553DivisorDegree S E :=
  map_add (s1553DegreeHom S) D E

theorem s1553DivisorDegree_neg (D : s1553CurveDivisor S) :
    s1553DivisorDegree S (-D) = -s1553DivisorDegree S D :=
  map_neg (s1553DegreeHom S) D

/-- The support of a sum of two unit point divisors is the pair of the points
(with the convention that the pair is a singleton when the points coincide). -/
theorem s1553PointDivisor_add_support (P Q : (s1423Model S).Point) :
    (s1553PointDivisor S P 1 + s1553PointDivisor S Q 1).support = {P, Q} := by
  ext R
  simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply,
    Finset.mem_insert, Finset.mem_singleton]
  by_cases hP : R = P
  · subst R
    by_cases hQ : P = Q
    · subst Q
      simp [s1553PointDivisor]
    · simp [hQ, s1553PointDivisor]
  · by_cases hQ : R = Q
    · subst R
      simp [hP, s1553PointDivisor]
    · simp [hP, hQ, s1553PointDivisor]

/-- The degree of a sum of two unit point divisors is two. -/
theorem s1553PointDivisor_add_degree (P Q : (s1423Model S).Point) :
    s1553DivisorDegree S
      (s1553PointDivisor S P 1 + s1553PointDivisor S Q 1) = 2 := by
  rw [s1553DivisorDegree_add, s1553DivisorDegree_single,
    s1553DivisorDegree_single]
  norm_num

/-! ## 2. The actual puncture ideal is maximal, and its comparison -/

/-- The affine point ideal of a nonsingular point is maximal: its quotient is
the base field. -/
theorem s1553PointIdeal_isMaximal {x y : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y) :
    (CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y)).IsMaximal := by
  have hEq : Polynomial.eval x
      (Polynomial.eval (Polynomial.C y) (s1423Model S).polynomial) = 0 := h.1
  let q := CoordinateRing.quotientXYIdealEquiv (W' := s1423Model S)
    (x := x) (y := Polynomial.C y) hEq
  refine Ideal.Quotient.maximal_of_isField _ ?_
  exact MulEquiv.isField (Field.toIsField S.arithmetic.F) q.toRingEquiv

/-- Containment of actual affine point ideals is exactly equality of the
corresponding actual curve points. -/
theorem s1553PointIdeal_le_iff {x y qx qy : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y)
    (hq : (s1423Model S).Nonsingular qx qy) :
    CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y) ≤
      CoordinateRing.XYIdeal (s1423Model S) qx (Polynomial.C qy) ↔
    (Point.some qx qy hq : (s1423Model S).Point) = Point.some x y h := by
  classical
  constructor
  · intro hle
    have hIPmax := s1553PointIdeal_isMaximal S h
    have hIQmax := s1553PointIdeal_isMaximal S hq
    have hEq : CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y) =
        CoordinateRing.XYIdeal (s1423Model S) qx (Polynomial.C qy) :=
      Ideal.IsMaximal.eq_of_le hIPmax hIQmax.ne_top hle
    have hunits : CoordinateRing.XYIdeal' (W := s1423Model S) h =
        CoordinateRing.XYIdeal' (W := s1423Model S) hq := by
      ext
      rw [CoordinateRing.XYIdeal'_eq, CoordinateRing.XYIdeal'_eq, hEq]
    have hclasses : ClassGroup.mk (s1423Model S).FunctionField
          (CoordinateRing.XYIdeal' (W := s1423Model S) h) =
        ClassGroup.mk (s1423Model S).FunctionField
          (CoordinateRing.XYIdeal' (W := s1423Model S) hq) := by
      rw [hunits]
    have hpoint : (Point.some x y h : (s1423Model S).Point) =
        Point.some qx qy hq := by
      apply Point.toClass_injective
      rw [Point.toClass_some, Point.toClass_some]
      exact hclasses
    exact hpoint.symm
  · intro hQ
    have hx : qx = x := by
      injection hQ with hx _
    have hy : qy = y := by
      injection hQ with _ hy
    rw [hx, hy]

/-! ## 3. The actual section of the S1423 line bundle -/

/-- The actual affine section X - x of the S1423 line bundle at an affine
puncture P = (x, y). -/
noncomputable def s1553AffineSection {x y : S.arithmetic.F}
    {hns : (s1423Model S).Nonsingular x y}
    (h : sourcePunctureAffinePoint S = .some x y hns) : s1423Module S :=
  ⟨CoordinateRing.XClass (s1423Model S) x, by
    rw [sourcePunctureVanishingIdeal_of_some S h]
    exact Ideal.subset_span (by simp)⟩

theorem s1553AffineSection_val {x y : S.arithmetic.F}
    {hns : (s1423Model S).Nonsingular x y}
    (h : sourcePunctureAffinePoint S = .some x y hns) :
    (s1553AffineSection S h : s1423Ring S) =
      CoordinateRing.XClass (s1423Model S) x := rfl

theorem s1553AffineSection_ne_zero {x y : S.arithmetic.F}
    {hns : (s1423Model S).Nonsingular x y}
    (h : sourcePunctureAffinePoint S = .some x y hns) :
    s1553AffineSection S h ≠ 0 := by
  intro hzero
  have hval : CoordinateRing.XClass (s1423Model S) x = 0 := by
    rw [← s1553AffineSection_val S h]
    exact congrArg Subtype.val hzero
  exact CoordinateRing.XClass_ne_zero x hval

/-- The actual section 1 of the S1423 line bundle at the puncture at infinity. -/
noncomputable def s1553InfinitySection
    (h : sourcePunctureAffinePoint S = .zero) : s1423Module S :=
  ⟨1, by
    rw [sourcePunctureVanishingIdeal_of_zero S h]
    exact Submodule.mem_top⟩

theorem s1553InfinitySection_val (h : sourcePunctureAffinePoint S = .zero) :
    (s1553InfinitySection S h : s1423Ring S) = 1 := rfl

theorem s1553InfinitySection_ne_zero (h : sourcePunctureAffinePoint S = .zero) :
    s1553InfinitySection S h ≠ 0 := by
  intro hzero
  have hval : (1 : s1423Ring S) = 0 := by
    rw [← s1553InfinitySection_val S h]
    exact congrArg Subtype.val hzero
  exact one_ne_zero hval

/-! ## 4. The zero divisor of the S1423 section -/

/-- A section of the S1423 line bundle vanishes at an affine point Q when its
value lies in the point ideal of Q. -/
def s1553SectionVanishesAt (s : s1423Module S)
    (qx qy : S.arithmetic.F) : Prop :=
  (s : s1423Ring S) ∈
    CoordinateRing.XYIdeal (s1423Model S) qx (Polynomial.C qy)

/-- The affine zero locus of a section of the S1423 line bundle. -/
def s1553ZeroLocus (s : s1423Module S) : Set ((s1423Model S).Point) :=
  {Q | ∃ (qx qy : S.arithmetic.F) (hq : (s1423Model S).Nonsingular qx qy),
      Q = Point.some qx qy hq ∧ s1553SectionVanishesAt S s qx qy}

/-- The XClass membership criterion: X - x lies in the point ideal of Q exactly
when Q is P or -P. -/
theorem s1553XClass_mem_XYIdeal_iff {x y qx qy : S.arithmetic.F}
    (h : (s1423Model S).Nonsingular x y)
    (hq : (s1423Model S).Nonsingular qx qy) :
    CoordinateRing.XClass (s1423Model S) x ∈
      CoordinateRing.XYIdeal (s1423Model S) qx (Polynomial.C qy) ↔
    (Point.some qx qy hq : (s1423Model S).Point) =
        Point.some x y h ∨
      (Point.some qx qy hq : (s1423Model S).Point) =
        -Point.some x y h := by
  constructor
  · intro hmem
    have hspan : CoordinateRing.XIdeal (s1423Model S) x ≤
        CoordinateRing.XYIdeal (s1423Model S) qx (Polynomial.C qy) := by
      change Ideal.span {CoordinateRing.XClass (s1423Model S) x} ≤ _
      rw [Ideal.span_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hmem
    have hmul : CoordinateRing.XYIdeal (s1423Model S) x
          (Polynomial.C ((s1423Model S).negY x y)) *
        CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y) ≤
        CoordinateRing.XYIdeal (s1423Model S) qx (Polynomial.C qy) := by
      rw [CoordinateRing.XYIdeal_neg_mul h]
      exact hspan
    have hprime : (CoordinateRing.XYIdeal (s1423Model S) qx
        (Polynomial.C qy)).IsPrime :=
      (s1553PointIdeal_isMaximal S hq).isPrime
    rcases (Ideal.IsPrime.mul_le hprime).mp hmul with hleft | hright
    · right
      have hneg_ns : (s1423Model S).Nonsingular x ((s1423Model S).negY x y) :=
        (WeierstrassCurve.Affine.nonsingular_neg ..).mpr h
      have hle' := (s1553PointIdeal_le_iff S hneg_ns hq).mp hleft
      rw [hle']
      exact (Point.neg_some h).symm
    · left
      exact (s1553PointIdeal_le_iff S h hq).mp hright
  · rintro (hQ | hQ)
    · have hx : qx = x := by
        injection hQ with hx _
      rw [hx]
      exact Ideal.subset_span (by simp)
    · have hQ' : (Point.some qx qy hq : (s1423Model S).Point) =
          Point.some x ((s1423Model S).negY x y)
            ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr h) := by
        rw [hQ, Point.neg_some]
      have hx : qx = x := by
        injection hQ' with hx _
      rw [hx]
      exact Ideal.subset_span (by simp)

/-- The section X - x vanishes at Q exactly when Q is P or -P. -/
theorem s1553AffineSection_vanishes_iff {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y)
    (h : sourcePunctureAffinePoint S = .some x y hns)
    {qx qy : S.arithmetic.F} (hq : (s1423Model S).Nonsingular qx qy) :
    s1553SectionVanishesAt S (s1553AffineSection S h) qx qy ↔
      (Point.some qx qy hq : (s1423Model S).Point) =
          Point.some x y hns ∨
        (Point.some qx qy hq : (s1423Model S).Point) =
          -Point.some x y hns := by
  rw [s1553SectionVanishesAt, s1553AffineSection_val]
  exact s1553XClass_mem_XYIdeal_iff S hns hq

/-- The affine zero locus of X - x is exactly {P, -P}. -/
theorem s1553AffineSectionZeroLocus_eq {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y)
    (h : sourcePunctureAffinePoint S = .some x y hns) :
    s1553ZeroLocus S (s1553AffineSection S h) =
      {Point.some x y hns, -Point.some x y hns} := by
  ext Q
  constructor
  · rintro ⟨qx, qy, hq, rfl, hv⟩
    rcases (s1553AffineSection_vanishes_iff S hns h hq).mp hv with hQ | hQ
    · simp [hQ]
    · simp [hQ]
  · intro hQ
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hQ
    rcases hQ with rfl | rfl
    · exact ⟨x, y, hns, rfl,
        (s1553AffineSection_vanishes_iff S hns h hns).mpr (Or.inl rfl)⟩
    · let hneg : (s1423Model S).Nonsingular x ((s1423Model S).negY x y) :=
        (WeierstrassCurve.Affine.nonsingular_neg ..).mpr hns
      refine ⟨x, (s1423Model S).negY x y, hneg, ?_, ?_⟩
      · rw [Point.neg_some]
      · rw [s1553AffineSection_vanishes_iff S hns h hneg]
        right
        exact (Point.neg_some hns).symm

/-- The actual curve zero divisor of X - x: [P] + [-P]. -/
noncomputable def s1553AffineSectionZeroDivisor {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y) : s1553CurveDivisor S :=
  s1553PointDivisor S (Point.some x y hns) 1 +
    s1553PointDivisor S (-Point.some x y hns) 1

theorem s1553AffineSectionZeroDivisor_support {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y) :
    (s1553AffineSectionZeroDivisor S hns).support =
      {Point.some x y hns, -Point.some x y hns} :=
  s1553PointDivisor_add_support S _ _

theorem s1553AffineSectionZeroDivisor_degree {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y) :
    s1553DivisorDegree S (s1553AffineSectionZeroDivisor S hns) = 2 :=
  s1553PointDivisor_add_degree S _ _

theorem s1553AffineSectionZeroDivisor_ne_zero {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y) :
    s1553AffineSectionZeroDivisor S hns ≠ 0 := by
  intro hzero
  have hdeg := s1553AffineSectionZeroDivisor_degree S hns
  rw [hzero, s1553DivisorDegree_zero] at hdeg
  norm_num at hdeg

/-- The affine zero locus of the infinity section is empty. -/
theorem s1553InfinitySectionZeroLocus_eq
    (h : sourcePunctureAffinePoint S = .zero) :
    s1553ZeroLocus S (s1553InfinitySection S h) = ∅ := by
  ext Q
  constructor
  · rintro ⟨qx, qy, hq, rfl, hv⟩
    rw [s1553SectionVanishesAt, s1553InfinitySection_val S h] at hv
    exact (s1553PointIdeal_isMaximal S hq).ne_top
      ((Ideal.eq_top_iff_one _).mpr hv)
  · intro hmem
    simp at hmem

/-- The infinity section has zero affine zero divisor. -/
noncomputable def s1553InfinitySectionZeroDivisor :
    s1553CurveDivisor S :=
  0

theorem s1553InfinitySectionZeroDivisor_support :
    (s1553InfinitySectionZeroDivisor S).support = ∅ := by
  simp [s1553InfinitySectionZeroDivisor]

theorem s1553InfinitySectionZeroDivisor_degree :
    s1553DivisorDegree S (s1553InfinitySectionZeroDivisor S) = 0 := by
  simp [s1553InfinitySectionZeroDivisor]

/-! ## 5. The actual theta line bundle and its canonical global section -/

/-- The actual theta module: the dual of the actual puncture ideal module, i.e.
the module of the line bundle O(P) = (s1423LineBundle)^(-1). -/
abbrev s1553ThetaModule : Type u :=
  Module.Dual (s1423Ring S) (s1423Module S)

/-- The canonical global theta section: the inclusion of the puncture ideal
into the coordinate ring. -/
noncomputable def s1553ThetaSection : s1553ThetaModule S :=
  (sourcePunctureVanishingIdeal S).subtype

/-- The canonical theta section is nonzero. -/
theorem s1553ThetaSection_ne_zero : s1553ThetaSection S ≠ 0 := by
  intro hzero
  cases h : sourcePunctureAffinePoint S with
  | zero =>
      have hmem : (1 : s1423Ring S) ∈ sourcePunctureVanishingIdeal S := by
        rw [sourcePunctureVanishingIdeal_of_zero S h]
        exact Submodule.mem_top
      have h0 : (s1553ThetaSection S) ⟨1, hmem⟩ = 0 := by
        rw [hzero]
        rfl
      have hval : (1 : s1423Ring S) = 0 := by
        simpa [s1553ThetaSection] using h0
      exact one_ne_zero hval
  | some x y hns =>
      have hmem : CoordinateRing.XClass (s1423Model S) x ∈
          sourcePunctureVanishingIdeal S := by
        rw [sourcePunctureVanishingIdeal_of_some S h]
        exact Ideal.subset_span (by simp)
      have h0 : (s1553ThetaSection S)
          ⟨CoordinateRing.XClass (s1423Model S) x, hmem⟩ = 0 := by
        rw [hzero]
        rfl
      have hval : CoordinateRing.XClass (s1423Model S) x = 0 := by
        simpa [s1553ThetaSection] using h0
      exact CoordinateRing.XClass_ne_zero x hval

theorem s1553ThetaModule_invertible :
    Module.Invertible (s1423Ring S) (s1553ThetaModule S) := by
  letI : Module.Invertible (s1423Ring S) (s1423Module S) :=
    s1423Module_invertible S
  infer_instance

/-- The actual source-curve theta line bundle: the inverse of the S1423 line
bundle.  Its actual module carrier is s1553ThetaModule (the dual of the
actual puncture ideal module), whose Picard class is this inverse by
Pic.mk_dual and s1423ModuleClass_eq_lineBundle. -/
noncomputable def s1553ThetaLineBundle : CommRing.Pic (s1423Ring S) :=
  (s1423LineBundle S)⁻¹

/-- **The theta line bundle is the inverse of the S1423 line bundle.** -/
theorem s1553ThetaLineBundle_eq_inv_lineBundle :
    s1553ThetaLineBundle S = (s1423LineBundle S)⁻¹ := rfl

/-- A theta-section vanishes at an affine point Q when every value of the
section lies in the point ideal of Q. -/
def s1553ThetaSectionVanishesAt (s : s1553ThetaModule S)
    (qx qy : S.arithmetic.F) : Prop :=
  ∀ m : s1423Module S,
    s m ∈ CoordinateRing.XYIdeal (s1423Model S) qx (Polynomial.C qy)

/-- The affine theta zero locus. -/
def s1553ThetaZeroLocus : Set ((s1423Model S).Point) :=
  {Q | ∃ (qx qy : S.arithmetic.F) (hq : (s1423Model S).Nonsingular qx qy),
      Q = Point.some qx qy hq ∧
        s1553ThetaSectionVanishesAt S (s1553ThetaSection S) qx qy}

/-- The canonical theta section vanishes at Q exactly when the puncture ideal
is contained in the point ideal of Q. -/
theorem s1553ThetaSection_vanishes_iff {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y)
    (h : sourcePunctureAffinePoint S = .some x y hns)
    {qx qy : S.arithmetic.F} (hq : (s1423Model S).Nonsingular qx qy) :
    s1553ThetaSectionVanishesAt S (s1553ThetaSection S) qx qy ↔
      CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y) ≤
        CoordinateRing.XYIdeal (s1423Model S) qx (Polynomial.C qy) := by
  constructor
  · intro hv
    rw [CoordinateRing.XYIdeal, Ideal.span_le]
    intro z hz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have hmem : CoordinateRing.XClass (s1423Model S) x ∈
          sourcePunctureVanishingIdeal S := by
        rw [sourcePunctureVanishingIdeal_of_some S h]
        exact Ideal.subset_span (by simp)
      exact hv ⟨_, hmem⟩
    · have hmem : CoordinateRing.YClass (s1423Model S) (Polynomial.C y) ∈
          sourcePunctureVanishingIdeal S := by
        rw [sourcePunctureVanishingIdeal_of_some S h]
        exact Ideal.subset_span (by simp)
      exact hv ⟨_, hmem⟩
  · intro hle m
    let e : ↥(sourcePunctureVanishingIdeal S) ≃ₗ[s1423Ring S]
        ↥(CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y)) :=
      LinearEquiv.ofEq _ _ (sourcePunctureVanishingIdeal_of_some S h)
    have hm : (e m : s1423Ring S) ∈
        CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y) := (e m).2
    have hcoe : (e m : s1423Ring S) = (m : s1423Ring S) := rfl
    simpa [s1553ThetaSection, hcoe] using hle hm

/-- At an affine puncture, the canonical theta section vanishes exactly at P. -/
theorem s1553ThetaSection_vanishes_iff_point {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y)
    (h : sourcePunctureAffinePoint S = .some x y hns)
    {qx qy : S.arithmetic.F} (hq : (s1423Model S).Nonsingular qx qy) :
    s1553ThetaSectionVanishesAt S (s1553ThetaSection S) qx qy ↔
      (Point.some qx qy hq : (s1423Model S).Point) =
        Point.some x y hns := by
  rw [s1553ThetaSection_vanishes_iff S hns h hq]
  exact s1553PointIdeal_le_iff S hns hq

/-- The affine zero locus of the canonical theta section is exactly {P}. -/
theorem s1553ThetaZeroLocus_eq_affine {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y)
    (h : sourcePunctureAffinePoint S = .some x y hns) :
    s1553ThetaZeroLocus S = {Point.some x y hns} := by
  ext Q
  constructor
  · rintro ⟨qx, qy, hq, rfl, hv⟩
    have hQ := (s1553ThetaSection_vanishes_iff_point S hns h hq).mp hv
    simp [hQ]
  · intro hQ
    rw [Set.mem_singleton_iff] at hQ
    rw [hQ]
    exact ⟨x, y, hns, rfl,
      (s1553ThetaSection_vanishes_iff_point S hns h hns).mpr rfl⟩

/-- At infinity, the canonical theta section has no affine zeros. -/
theorem s1553ThetaZeroLocus_eq_empty_infinity
    (h : sourcePunctureAffinePoint S = .zero) :
    s1553ThetaZeroLocus S = ∅ := by
  ext Q
  constructor
  · rintro ⟨qx, qy, hq, rfl, hv⟩
    have hmem : (1 : s1423Ring S) ∈ sourcePunctureVanishingIdeal S := by
      rw [sourcePunctureVanishingIdeal_of_zero S h]
      exact Submodule.mem_top
    have hone : (1 : s1423Ring S) ∈
        CoordinateRing.XYIdeal (s1423Model S) qx (Polynomial.C qy) := by
      have hv1 := hv ⟨1, hmem⟩
      simpa [s1553ThetaSection] using hv1
    exact (s1553PointIdeal_isMaximal S hq).ne_top
      ((Ideal.eq_top_iff_one _).mpr hone)
  · intro hmem
    simp at hmem

/-- The actual curve zero divisor of the canonical theta section at an affine
puncture: [P], of degree one. -/
noncomputable def s1553ThetaAffineZeroDivisor {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y) : s1553CurveDivisor S :=
  s1553PointDivisor S (Point.some x y hns) 1

theorem s1553ThetaAffineZeroDivisor_support {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y) :
    (s1553ThetaAffineZeroDivisor S hns).support = {Point.some x y hns} := by
  rw [s1553ThetaAffineZeroDivisor, s1553PointDivisor]
  exact Finsupp.support_single (Point.some x y hns) (by norm_num : (1 : ℤ) ≠ 0)

theorem s1553ThetaAffineZeroDivisor_degree {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y) :
    s1553DivisorDegree S (s1553ThetaAffineZeroDivisor S hns) = 1 := by
  simp [s1553ThetaAffineZeroDivisor]

theorem s1553ThetaAffineZeroDivisor_ne_zero {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y) :
    s1553ThetaAffineZeroDivisor S hns ≠ 0 := by
  intro hzero
  have hdeg := s1553ThetaAffineZeroDivisor_degree S hns
  rw [hzero, s1553DivisorDegree_zero] at hdeg
  norm_num at hdeg

/-- The infinity theta divisor is zero on the affine chart. -/
noncomputable def s1553ThetaInfinityZeroDivisor : s1553CurveDivisor S :=
  0

theorem s1553ThetaInfinityZeroDivisor_support :
    (s1553ThetaInfinityZeroDivisor S).support = ∅ := by
  simp [s1553ThetaInfinityZeroDivisor]

theorem s1553ThetaInfinityZeroDivisor_degree :
    s1553DivisorDegree S (s1553ThetaInfinityZeroDivisor S) = 0 := by
  simp [s1553ThetaInfinityZeroDivisor]

/-! ## 6. The q_v^(j^2) weighted curve divisor and the degree obstruction -/

/-- The curve-level candidate for the q_v^(j^2) divisor: for a map from the
signed labels to actual source-curve points, put coefficient j^2 at the image
of j.  This is the precise naive geometric realization of the q_j2 family. -/
noncomputable def s1553QJ2WeightedCurveDivisor
    (φ : SignedLabel l.value → (s1423Model S).Point) :
    s1553CurveDivisor S :=
  ∑ j : SignedLabel l.value,
    (gaussExponent j.1).toNat • s1553PointDivisor S (φ j) 1

/-- The degree of the q_j2 weighted curve divisor is the sum of the j^2
weights, independent of the chosen points. -/
theorem s1553QJ2WeightedCurveDivisor_degree
    (φ : SignedLabel l.value → (s1423Model S).Point) :
    s1553DivisorDegree S (s1553QJ2WeightedCurveDivisor S φ) =
      ((∑ j : SignedLabel l.value, (gaussExponent j.1).toNat : ℕ) : ℤ) := by
  unfold s1553QJ2WeightedCurveDivisor
  change s1553DegreeHom S (∑ j : SignedLabel l.value,
    (gaussExponent j.1).toNat • s1553PointDivisor S (φ j) 1) = _
  rw [map_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_nsmul, s1553DegreeHom_single]
  simp

/-- The label half-width is at least two. -/
theorem s1553LStar_two_le : 2 ≤ lStar l.value := by
  have h5 := l.ge_five
  unfold lStar
  omega

/-- The signed label 2 exists for every prime l >= 5. -/
noncomputable def s1553LabelTwo : SignedLabel l.value :=
  ⟨2, by
    constructor
    · have h : (0 : ℤ) ≤ (lStar l.value : ℤ) := by
        exact_mod_cast Nat.zero_le _
      omega
    · exact_mod_cast s1553LStar_two_le (l := l)⟩

theorem s1553LabelTwo_gauss :
    (gaussExponent (s1553LabelTwo (l := l)).1).toNat = 4 := by
  simp [s1553LabelTwo, gaussExponent]

/-- The sum of the j^2 weights is at least four. -/
theorem s1553QJ2Weight_sum_ge_four :
    4 ≤ ∑ j : SignedLabel l.value, (gaussExponent j.1).toNat := by
  have hmem : s1553LabelTwo (l := l) ∈
      (Finset.univ : Finset (SignedLabel l.value)) :=
    Finset.mem_univ _
  have hle := Finset.single_le_sum
    (f := fun j : SignedLabel l.value => (gaussExponent j.1).toNat)
    (fun _ _ => Nat.zero_le _) hmem
  rwa [s1553LabelTwo_gauss] at hle

theorem s1553QJ2Weight_sum_ne_one :
    (∑ j : SignedLabel l.value, (gaussExponent j.1).toNat) ≠ 1 := by
  have h4 := s1553QJ2Weight_sum_ge_four (l := l)
  omega

theorem s1553QJ2Weight_sum_ne_two :
    (∑ j : SignedLabel l.value, (gaussExponent j.1).toNat) ≠ 2 := by
  have h4 := s1553QJ2Weight_sum_ge_four (l := l)
  omega

theorem s1553QJ2WeightedCurveDivisor_degree_ne_one
    (φ : SignedLabel l.value → (s1423Model S).Point) :
    s1553DivisorDegree S (s1553QJ2WeightedCurveDivisor S φ) ≠ 1 := by
  rw [s1553QJ2WeightedCurveDivisor_degree]
  have h := s1553QJ2Weight_sum_ne_one (l := l)
  omega

theorem s1553QJ2WeightedCurveDivisor_degree_ne_two
    (φ : SignedLabel l.value → (s1423Model S).Point) :
    s1553DivisorDegree S (s1553QJ2WeightedCurveDivisor S φ) ≠ 2 := by
  rw [s1553QJ2WeightedCurveDivisor_degree]
  have h := s1553QJ2Weight_sum_ne_two (l := l)
  omega

/-- The actual theta divisor [P] cannot be a q_j2 weighted point divisor. -/
theorem s1553ThetaAffineZeroDivisor_ne_qj2Weighted {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y)
    (φ : SignedLabel l.value → (s1423Model S).Point) :
    s1553ThetaAffineZeroDivisor S hns ≠
      s1553QJ2WeightedCurveDivisor S φ := by
  intro heq
  have h1 : s1553DivisorDegree S (s1553ThetaAffineZeroDivisor S hns) = 1 :=
    s1553ThetaAffineZeroDivisor_degree S hns
  have h1' : s1553DivisorDegree S
      (s1553QJ2WeightedCurveDivisor S φ) = 1 := by
    rw [← heq]
    exact h1
  rw [s1553QJ2WeightedCurveDivisor_degree] at h1'
  have hne := s1553QJ2Weight_sum_ne_one (l := l)
  omega

/-- The S1423 section divisor [P] + [-P] cannot be a q_j2 weighted point
divisor. -/
theorem s1553AffineSectionZeroDivisor_ne_qj2Weighted
    {x y : S.arithmetic.F} (hns : (s1423Model S).Nonsingular x y)
    (φ : SignedLabel l.value → (s1423Model S).Point) :
    s1553AffineSectionZeroDivisor S hns ≠
      s1553QJ2WeightedCurveDivisor S φ := by
  intro heq
  have h1 : s1553DivisorDegree S (s1553AffineSectionZeroDivisor S hns) = 2 :=
    s1553AffineSectionZeroDivisor_degree S hns
  have h1' : s1553DivisorDegree S
      (s1553QJ2WeightedCurveDivisor S φ) = 2 := by
    rw [← heq]
    exact h1
  rw [s1553QJ2WeightedCurveDivisor_degree] at h1'
  have hne := s1553QJ2Weight_sum_ne_two (l := l)
  omega

/-! ## 7. The naive q_j2 realization types are empty -/

/-- A naive curve-level realization of the q_j2 theta divisor: a label-to-point
map whose weighted point divisor equals the actual theta divisor [P]. -/
abbrev s1553NaiveQJ2ThetaRealization {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y) : Type u :=
  { φ : SignedLabel l.value → (s1423Model S).Point //
    s1553QJ2WeightedCurveDivisor S φ =
      s1553ThetaAffineZeroDivisor S hns }

/-- There is no naive q_j2 realization of the actual theta divisor [P]. -/
theorem s1553NaiveQJ2ThetaRealization_empty {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y) :
    IsEmpty (s1553NaiveQJ2ThetaRealization S hns) := by
  constructor
  rintro ⟨φ, hφ⟩
  exact s1553ThetaAffineZeroDivisor_ne_qj2Weighted S hns φ hφ.symm

/-- A naive curve-level realization of the q_j2 theta divisor at the S1423
section divisor [P] + [-P]. -/
abbrev s1553NaiveQJ2S1423SectionRealization {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y) : Type u :=
  { φ : SignedLabel l.value → (s1423Model S).Point //
    s1553QJ2WeightedCurveDivisor S φ =
      s1553AffineSectionZeroDivisor S hns }

/-- There is no naive q_j2 realization of the S1423 section divisor
[P] + [-P]. -/
theorem s1553NaiveQJ2S1423SectionRealization_empty
    {x y : S.arithmetic.F} (hns : (s1423Model S).Nonsingular x y) :
    IsEmpty (s1553NaiveQJ2S1423SectionRealization S hns) := by
  constructor
  rintro ⟨φ, hφ⟩
  exact s1553AffineSectionZeroDivisor_ne_qj2Weighted S hns φ hφ.symm

/-! ## 8. The analytic theta is not the source-curve theta -/

/-- Re-export: the analytic theta zero locus of S1424 is empty. -/
theorem s1553AnalyticThetaZeroLocus_empty :
    s1424AnalyticThetaZeroLocus = ∅ :=
  s1424AnalyticThetaZeroLocus_empty

/-- Re-export: the label-indexed q_v^(j^2) divisor of S1424 is zero: the unit
family has no zero coefficient. -/
theorem s1553QJ2LabelDivisor_eq_zero :
    s1424QJ2Divisor (l := l) = 0 :=
  s1424QJ2Divisor_eq_zero (l := l)

/-- The analytic theta has empty zero locus, while the actual source-curve
theta divisor [P] is nonzero.  The analytic theta cannot be substituted for
the source-curve theta without a new geometric comparison. -/
theorem s1553AnalyticTheta_not_sourceCurveTheta {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y) :
    s1424AnalyticThetaZeroLocus = ∅ ∧
      s1553ThetaAffineZeroDivisor S hns ≠ 0 :=
  ⟨s1553AnalyticThetaZeroLocus_empty,
    s1553ThetaAffineZeroDivisor_ne_zero S hns⟩

/-! ## 9. Exact first missing geometric object: boundary statement -/

/-- **Boundary.**  At an affine puncture:

* the analytic theta zero locus is empty;
* the actual source-curve theta divisor [P] is nonzero;
* no naive q_j2 weighted point divisor realizes [P].

Hence the exact first missing geometric object is a genuinely different
curve-level geometric theta divisor together with its q_v^(j^2) comparison, not
the analytic theta section and not the naive q_j2 weighted divisor. -/
theorem s1553ExactFirstMissingBoundary {x y : S.arithmetic.F}
    (hns : (s1423Model S).Nonsingular x y) :
    s1424AnalyticThetaZeroLocus = ∅ ∧
      s1553ThetaAffineZeroDivisor S hns ≠ 0 ∧
      IsEmpty (s1553NaiveQJ2ThetaRealization S hns) :=
  ⟨s1553AnalyticThetaZeroLocus_empty,
    s1553ThetaAffineZeroDivisor_ne_zero S hns,
    s1553NaiveQJ2ThetaRealization_empty S hns⟩

end ABCBridge.S1553SourceCurveThetaActual

end
