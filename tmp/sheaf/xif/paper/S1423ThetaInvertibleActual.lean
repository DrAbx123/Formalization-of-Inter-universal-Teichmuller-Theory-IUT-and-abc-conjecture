/-
# S1423: source-curve line bundle via Mathlib invertible modules, fractional ideals,
the ideal class group and the Picard group

## Actual donors

The actual Definition 3.1 source S, its Weierstrass model W = s1423Model S, the
affine coordinate ring R = s1423Ring S (the S1401 coordinate ring
WeierstrassCurve.Affine.CoordinateRing), the puncture s1423Point S, the puncture
ideal sourcePunctureVanishingIdeal S and its module sourcePunctureIdealModule S are
the donors of S1401 and SourceQlThetaPunctureIdeal.  No source datum beyond
Definition 3.1 is assumed and no object is invented.

## What is constructed (actual data, no gate)

* s1423PointClassAt S P : Additive (ClassGroup R) for every actual point
  P : W.Point: Mathlib's WeierstrassCurve.Affine.Point.toClass, the class of the
  nonzero fractional ideal <X - x, Y - y> (CoordinateRing.XYIdeal').
* s1423LineBundleAt S P : CommRing.Pic R: the actual line bundle at P, the image
  of the point class under ClassGroup.equivPic R.  This is a genuine element of
  the Picard group of the actual coordinate ring, i.e. a line bundle on the affine
  chart of the source curve up to isomorphism.  It is built from Mathlib's
  fractional-ideal / class-group / Picard machinery, not from an arbitrary carrier.
* s1423LineBundle S := s1423LineBundleAt S (s1423Point S): the line bundle at the
  actual puncture of the source curve.
* the underlying rank-one projective module
  s1423Module S = sourcePunctureIdealModule S = the puncture ideal module, with
  Module.Invertible, Module.Projective, Module.Finite, Module.finrank = 1, and its
  Picard class s1423ModuleClass S = Pic.mk R (s1423Module S).

## What is proved

* s1423LineBundleAt_zero, s1423LineBundleAt_add: P maps to O(P) is a group
  homomorphism from the actual point group W.Point to Pic R.
* s1423LineBundleAt_eq_one_iff, s1423LineBundleAt_injective: the line bundle is
  trivial exactly at the origin, and P maps to O(P) is injective; hence a
  non-origin puncture gives a nontrivial line bundle
  (s1423LineBundle_ne_one_of_ne_zero).
* s1423ModuleClass_eq_lineBundle: the Picard class of the actual rank-one
  projective module equals the class-group line bundle of the puncture.  The
  bridge uses two Mathlib-adjacent computations proved here:
  s1423_unitsToPic_eq_equivPic_symm (Submodule.unitsToPic of a unit submodule is
  ClassGroup.equivPic of its class) and
  s1423_mulEquivUnitsSubmoduleQuotRange_mk (the class-group/Picard comparison sends
  ClassGroup.mk of a fractional ideal to the class of the corresponding unit
  submodule).

## Exact first missing field

S1401 recorded the first missing source datum as the item curveLineBundle of
SourceThetaLineBundleMissingDatum.  That item is constructed here
(s1423LineBundle), not assumed; s1423CurveLineBundle_noLongerMissing records that
it left the missing list.  The exact next missing field, recorded by the actual
source data, is the theta object item:

* a theta structure/global section on the constructed line bundle whose zero
  divisor is the geometric theta divisor {q_v^(j^2)} (item thetaObjectATheta),
  followed by the geometric theta divisor carrier itself (item
  geometricThetaDivisor).

The only divisor carrier supplied by the source is the arithmetic divisor
SourceThetaDivisor S = (NumberField.InfinitePlace S.arithmetic.F -> Z)
(s1423DivisorType_eq), and the theta values available in the tree are the unit
family SignedLabel l.value -> R^times.  There is no theta section of the
constructed line bundle and no equality of its zero divisor with the geometric
theta divisor in the current source contract.  The remaining named items are
s1423RemainingThetaMissingData S (the S1401 list with curveLineBundle removed).
No Nonempty gate, no propositional placeholder and no fake line bundle, theta
object or theta section is introduced.

Source anchors: IUT I Definition 3.1; IUT II p.2-3 and Remark 2.5.1 (theta values
q_v^(j^2)); IUT III Definition 3.8 and Corollary 3.12 (theta-pilot divisor);
S1401 and S1409 for the actual donors.
-/
import Mathlib.RingTheory.PicardGroup
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffinePunctureIdealInvertible
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaPunctureIdeal
import tmp.sheaf.xif.paper.S1401ThetaLineBundleActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace ABCBridge.S1423ThetaInvertibleActual

open CommRing Pic
open WeierstrassCurve.Affine
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open ABCBridge.SourceQlThetaPunctureIdeal
open ABCBridge.S1401ThetaLineBundleActual
open ABCBridge.SourceQlThetaLineBundleFromCurve

attribute [local instance] Classical.decEq

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data.{u} l)

/-! ## 1. Actual donors -/

/-- Actual affine coordinate ring of the source Weierstrass model. -/
abbrev s1423Ring : Type u :=
  sourcePunctureCoordinateRing S

/-- Actual affine Weierstrass model of the source curve. -/
abbrev s1423Model : WeierstrassCurve.Affine S.arithmetic.F :=
  sourcePunctureAffineModel S

/-- Actual puncture of the source Weierstrass model. -/
abbrev s1423Point : (s1423Model S).Point :=
  sourcePunctureAffinePoint S

/-- The actual coordinate ring is a domain: the source base field is a field. -/
theorem s1423Ring_isDomain : IsDomain (s1423Ring S) :=
  inferInstance

/-- The actual source-curve module carrier of the puncture ideal. -/
abbrev s1423Module : Type u :=
  sourcePunctureIdealModule S

/-! ## 2. Fractional ideal, ideal class group and Picard group bridges

These computations are the missing glue between Mathlib's fractional-ideal/Picard
API and the class-group map Point.toClass.  They are proved from the actual
Mathlib definitions, not assumed. -/

section Bridges

variable {R : Type u} [CommRing R] [IsDomain R]

/-- The unit groups of submodules of the function field are commutative, so every
subgroup, in particular the range of the principal submodules, is normal. -/
instance s1423SubmoduleUnits_comm : IsMulCommutative ((Submodule R (FractionRing R))ˣ) :=
  IsMulCommutative.of_comm fun a b =>
    Units.ext (Submodule.mul_comm
      (M := (a : Submodule R (FractionRing R))) (N := (b : Submodule R (FractionRing R))))

/-- The range in (Submodule R (FractionRing R))^x of the principal submodules,
i.e. the denominator of the relative Picard group of R inside FractionRing R. -/
abbrev s1423SubmoduleUnitsSubgroup : Subgroup ((Submodule R (FractionRing R))ˣ) :=
  (Units.map (Submodule.spanSingleton (R := R) (A := FractionRing R)).toMonoidHom).range

/-- Submodule.unitsToPic of an invertible submodule of the function field is
ClassGroup.equivPic of its class in the ideal class group. -/
theorem s1423_unitsToPic_eq_equivPic_symm (I : (Submodule R (FractionRing R))ˣ) :
    ClassGroup.equivPic R ((ClassGroup.mulEquivUnitsSubmoduleQuotRange R).symm
        (QuotientGroup.mk' (s1423SubmoduleUnitsSubgroup (R := R)) I))
      = Submodule.unitsToPic R (FractionRing R) I := by
  classical
  rw [ClassGroup.equivPic_apply, MulEquiv.apply_symm_apply]
  rw [QuotientGroup.mk'_apply]
  rw [QuotientGroup.congr_apply]
  rw [MulEquiv.refl_apply]
  rw [QuotientGroup.mk'_apply]
  rw [QuotientGroup.quotientKerEquivRange]
  rw [MulEquiv.ofBijective_apply]
  rw [QuotientGroup.rangeKerLift]
  rw [QuotientGroup.lift_mk]
  rfl

/-- The class-group/Picard comparison ClassGroup.mulEquivUnitsSubmoduleQuotRange
sends ClassGroup.mk of a fractional ideal to the class of the corresponding unit
submodule of the function field. -/
theorem s1423_mulEquivUnitsSubmoduleQuotRange_mk
    (I : (FractionalIdeal (nonZeroDivisors R) (FractionRing R))ˣ) :
    (ClassGroup.mulEquivUnitsSubmoduleQuotRange R) (ClassGroup.mk (FractionRing R) I)
      = QuotientGroup.mk' (s1423SubmoduleUnitsSubgroup (R := R))
          (FractionalIdeal.unitsMulEquivSubmodule I) := by
  classical
  rw [ClassGroup.mk_def, FractionalIdeal.canonicalEquiv_self, RingEquiv.coe_monoidHom_refl,
    Units.map_id, MonoidHom.id_apply]
  exact show (QuotientGroup.congr (toPrincipalIdeal R (FractionRing R)).range
        (s1423SubmoduleUnitsSubgroup (R := R)) FractionalIdeal.unitsMulEquivSubmodule _)
      (QuotientGroup.mk' (toPrincipalIdeal R (FractionRing R)).range I)
    = QuotientGroup.mk' (s1423SubmoduleUnitsSubgroup (R := R))
        (FractionalIdeal.unitsMulEquivSubmodule I) from rfl

end Bridges

/-- The Picard class of the actual point ideal module is the line bundle class of
the point: it equals ClassGroup.equivPic of the nonzero fractional ideal
<X - x, Y - y>. -/
theorem s1423_pointIdeal_pic_eq_equivPic {F : Type u} [Field F]
    (W : WeierstrassCurve.Affine F) {x y : F} (h : W.Nonsingular x y)
    [Module.Invertible W.CoordinateRing
      ↥(CoordinateRing.XYIdeal W x (Polynomial.C y))] :
    Pic.mk W.CoordinateRing (↥(CoordinateRing.XYIdeal W x (Polynomial.C y)))
      = ClassGroup.equivPic W.CoordinateRing
          (ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' (W := W) h)) := by
  classical
  have h1 : Pic.mk W.CoordinateRing (↥(CoordinateRing.XYIdeal W x (Polynomial.C y)))
      = Submodule.unitsToPic W.CoordinateRing W.FunctionField
          (FractionalIdeal.unitsMulEquivSubmodule
            (CoordinateRing.XYIdeal' (W := W) h)) := by
    refine (Pic.mk_eq_mk_iff (R := W.CoordinateRing)).mpr ⟨?_⟩
    exact (LeanFormal.IUT.AffinePunctureIdeal.idealFractionalLinearEquiv W
      (CoordinateRing.XYIdeal W x (Polynomial.C y))).trans
        (LinearEquiv.ofEq _ _ (by rfl))
  rw [h1]
  have hA := s1423_unitsToPic_eq_equivPic_symm (R := W.CoordinateRing)
    (FractionalIdeal.unitsMulEquivSubmodule (CoordinateRing.XYIdeal' (W := W) h))
  have hB := s1423_mulEquivUnitsSubmoduleQuotRange_mk (R := W.CoordinateRing)
    (CoordinateRing.XYIdeal' (W := W) h)
  rw [← hA]
  congr 1
  rw [← hB]
  exact MulEquiv.symm_apply_apply _ _

/-! ## 3. The line bundle at an actual source-curve point -/

/-- The actual point class P maps to the class of <X - x, Y - y> in the ideal
class group of the source affine coordinate ring. -/
noncomputable def s1423PointClassAt (P : (s1423Model S).Point) :
    Additive (ClassGroup (s1423Ring S)) := by
  classical
  exact Point.toClass P

/-- The actual line bundle O(P) at a point, as an element of the Picard group of
the source affine coordinate ring. -/
noncomputable def s1423LineBundleAt (P : (s1423Model S).Point) :
    CommRing.Pic (s1423Ring S) :=
  ClassGroup.equivPic (s1423Ring S) (Additive.toMul (s1423PointClassAt S P))

/-- The actual source-curve line bundle at the puncture. -/
noncomputable def s1423LineBundle : CommRing.Pic (s1423Ring S) :=
  s1423LineBundleAt S (s1423Point S)

/-- The line bundle at the origin is trivial. -/
theorem s1423LineBundleAt_zero : s1423LineBundleAt S 0 = 1 := by
  rw [s1423LineBundleAt, s1423PointClassAt, Point.toClass_zero, toMul_zero]
  exact map_one _

/-- P maps to O(P) is a group homomorphism from the point group of the source
curve to the Picard group of its affine coordinate ring. -/
theorem s1423LineBundleAt_add (P Q : (s1423Model S).Point) :
    s1423LineBundleAt S (P + Q) = s1423LineBundleAt S P * s1423LineBundleAt S Q := by
  rw [s1423LineBundleAt, s1423LineBundleAt, s1423LineBundleAt,
    s1423PointClassAt, s1423PointClassAt, s1423PointClassAt]
  rw [map_add, toMul_add, map_mul]

/-- The line bundle at P is trivial exactly when P is the origin. -/
theorem s1423LineBundleAt_eq_one_iff (P : (s1423Model S).Point) :
    s1423LineBundleAt S P = 1 ↔ P = 0 := by
  rw [s1423LineBundleAt, s1423PointClassAt, MulEquiv.map_eq_one_iff, toMul_eq_one,
    Point.toClass_eq_zero]

/-- P maps to O(P) is injective: the line bundle remembers the point. -/
theorem s1423LineBundleAt_injective : Function.Injective (s1423LineBundleAt S) := by
  intro P Q hPQ
  have hPQ' : ClassGroup.equivPic (s1423Ring S) (Additive.toMul (s1423PointClassAt S P))
      = ClassGroup.equivPic (s1423Ring S) (Additive.toMul (s1423PointClassAt S Q)) := hPQ
  have h1 : Additive.toMul (s1423PointClassAt S P)
      = Additive.toMul (s1423PointClassAt S Q) :=
    (ClassGroup.equivPic (s1423Ring S)).injective hPQ'
  have h2 : s1423PointClassAt S P = s1423PointClassAt S Q :=
    Additive.toMul.injective h1
  have h3 : Point.toClass P = Point.toClass Q := h2
  exact Point.toClass_injective h3

/-- The actual line bundle at the puncture is nontrivial whenever the puncture is
not the origin. -/
theorem s1423LineBundle_ne_one_of_ne_zero (h : s1423Point S ≠ 0) :
    s1423LineBundle S ≠ 1 := by
  rw [s1423LineBundle]
  exact fun h1 => h ((s1423LineBundleAt_eq_one_iff S (s1423Point S)).mp h1)

/-! ## 4. The underlying rank-one projective module and its Picard class -/

/-- The actual puncture module is invertible (rank-one projective). -/
theorem s1423Module_invertible : Module.Invertible (s1423Ring S) (s1423Module S) :=
  sourcePunctureIdeal_invertible S

/-- The actual puncture module is projective. -/
theorem s1423Module_projective : Module.Projective (s1423Ring S) (s1423Module S) :=
  sourcePunctureIdeal_projective S

/-- The actual puncture module is finite. -/
theorem s1423Module_finite : Module.Finite (s1423Ring S) (s1423Module S) :=
  sourcePunctureIdeal_finite S

/-- The actual puncture module has rank one. -/
theorem s1423Module_finrank_one : Module.finrank (s1423Ring S) (s1423Module S) = 1 :=
  sourcePunctureIdeal_finrank_eq_one S

/-- The actual rank-one projective module is a line bundle. -/
theorem s1423Module_projective_rankOne :
    Module.Projective (s1423Ring S) (s1423Module S)
      ∧ Module.finrank (s1423Ring S) (s1423Module S) = 1 :=
  ⟨s1423Module_projective S, s1423Module_finrank_one S⟩

/-- The Picard class of the actual rank-one projective module. -/
noncomputable def s1423ModuleClass : CommRing.Pic (s1423Ring S) := by
  letI : Module.Invertible (s1423Ring S) (s1423Module S) := s1423Module_invertible S
  exact Pic.mk _ (s1423Module S)

/-- **Main identification**: the Picard class of the actual rank-one projective
module equals the class-group line bundle of the actual puncture.  So the
module-theoretic and the fractional-ideal/class-group/Picard constructions
produce the same line bundle. -/
theorem s1423ModuleClass_eq_lineBundle : s1423ModuleClass S = s1423LineBundle S := by
  classical
  rcases hP : s1423Point S with _ | ⟨x, y, h⟩
  · have hI : sourcePunctureVanishingIdeal S = (⊤ : Ideal (s1423Ring S)) :=
      sourcePunctureVanishingIdeal_of_zero S hP
    letI : Module.Invertible (s1423Ring S) (s1423Module S) := s1423Module_invertible S
    letI : Module.Invertible (s1423Ring S) (↥(⊤ : Ideal (s1423Ring S))) :=
      Module.Invertible.congr (Submodule.topEquiv (R := s1423Ring S) (M := s1423Ring S)).symm
    have hmod : s1423ModuleClass S = 1 := by
      show Pic.mk (s1423Ring S) (s1423Module S) = 1
      exact ((Pic.mk_eq_mk_iff (R := s1423Ring S)).mpr ⟨LinearEquiv.ofEq _ _ hI⟩).trans
        ((Pic.mk_eq_mk_iff (R := s1423Ring S)).mpr ⟨Submodule.topEquiv⟩ |>.trans
          (Pic.mk_self (R := s1423Ring S)))
    rw [hmod, s1423LineBundle, hP]
    exact (s1423LineBundleAt_zero S).symm
  · have hI : sourcePunctureVanishingIdeal S =
        CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y) :=
      sourcePunctureVanishingIdeal_of_some S hP
    letI : Module.Invertible (s1423Ring S) (s1423Module S) := s1423Module_invertible S
    letI : Module.Invertible (s1423Ring S)
        ↥(CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y)) :=
      LeanFormal.IUT.AffinePunctureIdeal.pointIdeal_invertible (s1423Model S) h
    have hmod : s1423ModuleClass S =
        Pic.mk (s1423Ring S)
          (↥(CoordinateRing.XYIdeal (s1423Model S) x (Polynomial.C y))) := by
      show Pic.mk (s1423Ring S) (s1423Module S) = _
      exact (Pic.mk_eq_mk_iff (R := s1423Ring S)).mpr ⟨LinearEquiv.ofEq _ _ hI⟩
    rw [hmod]
    rw [s1423_pointIdeal_pic_eq_equivPic (s1423Model S) h]
    rw [s1423LineBundle, s1423LineBundleAt, s1423PointClassAt, hP, Point.toClass_some]
    rfl

/-- The constructed line bundle is the Picard class of an actual invertible
(rank-one projective, finite) module. -/
theorem s1423LineBundle_eq_moduleClass :
    s1423LineBundle S = s1423ModuleClass S :=
  (s1423ModuleClass_eq_lineBundle S).symm

/-! ## 5. Exact first missing field: theta object and geometric theta divisor -/

/-- The only divisor carrier available from the actual source: integer
coefficient functions on the infinite places of the base field F.  This is an
arithmetic divisor on the number field, not a divisor on the source curve. -/
theorem s1423DivisorType_eq :
    s1401DivisorType S = (NumberField.InfinitePlace S.arithmetic.F → ℤ) := rfl

/-- The weighted theta degree of the actual zero divisor is zero. -/
theorem s1423ZeroDivisor_degree :
    s1401Degree S (s1401ZeroDivisor S) = 0 :=
  s1401ZeroDivisor_degree S

/-- The S1401 missing-data list with the item curveLineBundle removed: the line
bundle is constructed in this file. -/
def s1423RemainingThetaMissingData (S : SourceDefinition31Data.{u} l) :
    List SourceThetaLineBundleMissingDatum :=
  [ SourceThetaLineBundleMissingDatum.thetaObjectATheta,
    SourceThetaLineBundleMissingDatum.geometricThetaDivisor,
    SourceThetaLineBundleMissingDatum.unitComparisonMqMTheta,
    SourceThetaLineBundleMissingDatum.muTwoLDeckRootAction,
    SourceThetaLineBundleMissingDatum.conjugateSynchronization ]

/-- The remaining list is exactly the tail of the S1401 list. -/
theorem s1423RemainingThetaMissingData_eq_tail :
    sourceThetaLineBundleMissingData S =
      SourceThetaLineBundleMissingDatum.curveLineBundle ::
        s1423RemainingThetaMissingData S :=
  rfl

/-- Exactly five theta items remain after the line bundle is constructed. -/
theorem s1423RemainingThetaMissingData_length :
    (s1423RemainingThetaMissingData S).length = 5 :=
  rfl

/-- The line-bundle item is no longer missing: it is constructed in this file, so
it does not occur in the remaining list. -/
theorem s1423CurveLineBundle_noLongerMissing :
    SourceThetaLineBundleMissingDatum.curveLineBundle ∉ s1423RemainingThetaMissingData S := by
  simp [s1423RemainingThetaMissingData]

/-- The exact first missing field: a theta structure/global section on the
constructed line bundle, i.e. item thetaObjectATheta.  The theta section must have
zero divisor the geometric theta divisor {q_v^(j^2)}; the source supplies no
divisor on the curve (s1423DivisorType_eq is an arithmetic divisor on F), no theta
section of s1423LineBundle, and no such zero-divisor equality.  This is the named
first datum, not a propositional gate: the line bundle itself is constructed
above. -/
def s1423FirstMissingField : List SourceThetaLineBundleMissingDatum :=
  [ SourceThetaLineBundleMissingDatum.thetaObjectATheta ]

/-- The remaining list starts with the theta object, followed by the geometric
theta divisor. -/
theorem s1423FirstMissingField_eq :
    s1423RemainingThetaMissingData S =
      SourceThetaLineBundleMissingDatum.thetaObjectATheta ::
        [ SourceThetaLineBundleMissingDatum.geometricThetaDivisor,
          SourceThetaLineBundleMissingDatum.unitComparisonMqMTheta,
          SourceThetaLineBundleMissingDatum.muTwoLDeckRootAction,
          SourceThetaLineBundleMissingDatum.conjugateSynchronization ] :=
  rfl

end ABCBridge.S1423ThetaInvertibleActual

end
