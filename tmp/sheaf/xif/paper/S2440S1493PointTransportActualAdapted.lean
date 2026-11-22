import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual
import tmp.sheaf.xif.paper.S2414ThreePointsDistinctActual

/-!
# S2440: the actual S1493 point transport of the S2412 three 2-torsion points

This file transports the three 2-torsion points constructed by S2412/S2414, which
live on W.map (algebraMap R (AlgebraicClosure R)), to the K-side point group
SideKPoint T b of S1550, using the actual pointTransport of S1550.

## The identification

S2412 is stated for an arbitrary field R and curve W over R.  The F-side curve of
S1550 is, by definition, the base change of T.arithmetic.curve along
F -> F_v := Completion (sectionFPlace T b) and then along F_v -> LF, where
LF := AlgebraicClosure (F_v).  Instantiating S2412/S2414 at

  R := F_v,  W := S2440FvCurve T b := (T.arithmetic.curve.baseChange F_v).curve,

the S2412 curve S2411WK W = W.map (algebraMap F_v (AlgebraicClosure F_v)) is
*definitionally* the affine curve underlying the S1550 F-side projective curve
WFproj; both are T.arithmetic.curve mapped along F -> F_v -> LF.  The
identification is S2440_curve_ident / S2440_curve_ident_sideF /
S2440_curve_ident_trans, and each is proved by rfl.  No map between algebraic
closures enters: the algebraic closure of the field at which S2412 is instantiated
is literally LF.

## What is constructed

* S2440AffinePoint is the S2412/S2354 point attached to a root of the
  base-changed 2-division polynomial, transported along the curve identity to the
  S1550 F-side affine curve.
* S2440SideFPoint is its image in SideFPoint T b under
  Projective.Point.toAffineAddEquiv (WFproj T b).
* S2440SideKPoint = pointTransport T b (S2440SideFPoint ...) is the K-side point.
* S2440sideKEquiv is the composite additive equivalence
  (S2411WK (S2440FvCurve T b)).toAffine.Point to SideKPoint T b obtained from the
  curve identification, toAffineAddEquiv and the actual pointTransport;
  S2440_S2412_transport applies it to the existential produced by
  S2412ThreePoints itself.
* S2440SideKPoint_two_nsmul, S2440SideKPoint_ne_zero and S2440SideKPoint_ne prove
  that 2 • P = 0, that the points are nonzero, and that they are pairwise
  distinct.  Each property is preserved along the additive equivalences
  S2440affineTransport, toAffineAddEquiv and pointTransport, and hence is a
  transported statement about the actual S2412/S2414 points, not a new claim.
* S2440_three_sideK_points combines them: three pairwise distinct nonzero
  K-side points of order two.

## Boundary: the exact point-level closure map that is *not* needed here

A route that starts from the three 2-torsion points of the *global* arithmetic
curve over AlgebraicClosure T.arithmetic.F would need a point-level ring map
AlgebraicClosure T.arithmetic.F ->+* LF compatible with the two structural maps
from T.arithmetic.F.  Such a map is *not constructed* in this file (and no
canonical one is available in the API: IsAlgClosed.lift would produce only a
Classical.choice-dependent map, with no compatibility lemma for the S1493/S1550
curve identification).  It is recorded as S2440GlobalClosureMap and
S2440MissingGlobalClosureMap below, with no inhabitant and no theorem about it.
The construction above does not use it, because instantiating S2412 at R = F_v
makes AlgebraicClosure R literally LF, so S2440_curve_ident_trans is rfl.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option maxErrors 40

open WeierstrassCurve
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual
open LeanFormal.IUT.XiFPaper.S1482KSideTateUniformizationActual
open LeanFormal.IUT.XiFPaper.S1493KSideTateTransportActual
open LeanFormal.IUT.XiFPaper.S1550TatePointComparisonFromClosureActual
open LeanFormal.IUT.XiFPaper.S2411PointBuildActual
open LeanFormal.IUT.XiFPaper.S2354TwoTorsionPointsActual
open LeanFormal.IUT.XiFPaper.S2358TwoTorsionOrderActual
open LeanFormal.IUT.XiFPaper.S2376ThreeRootsActual
open LeanFormal.IUT.XiFPaper.S2405RootEvalCorrectActual
open LeanFormal.IUT.XiFPaper.S2412ThreePointsTransportActual
open LeanFormal.IUT.XiFPaper.S2414ThreePointsDistinctActual

namespace LeanFormal.IUT.XiFPaper.S2440S1493PointTransportActualAdapted

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- LF is a field, hence has decidable equality; this is the instance required by
Projective.Point.toAffineAddEquiv and by the affine point group law of Mathlib. -/
local instance s2440DecEqLF : DecidableEq (AlgebraicClosure (Fv T b)) := Classical.decEq _

/-! ## The S2412 input curve over F_v and its definitional identification with the
S1550 F-side curve -/

/-- The F-side curve base changed to the F-completion F_v: the Weierstrass curve
over F_v on which the S2412/S2414 constructions are run. -/
abbrev S2440FvCurve : WeierstrassCurve (Fv T b) :=
  (T.arithmetic.curve.baseChange (Fv T b)).curve

/-- The S2412 curve over AlgebraicClosure F_v is the base change of S2440FvCurve
to LF.  This is the point-level identification of the S2412 curve with the S1550
F-side curve; it is definitional (S2411WK W is W.map (algebraMap F_v LF) and
baseChange (LF T b) is the same map). -/
theorem S2440_curve_ident :
    S2411WK (S2440FvCurve T b) = (S2440FvCurve T b).baseChange (LF T b) := rfl

/-- The base change of S2440FvCurve to LF is the affine curve underlying the S1550
F-side projective curve WFproj; both are T.arithmetic.curve mapped along
F -> F_v -> LF. -/
theorem S2440_curve_ident_sideF :
    (S2440FvCurve T b).baseChange (LF T b) = (WFproj T b).toAffine := rfl

/-- The composite identification: the S2412 curve over AlgebraicClosure F_v is the
affine curve of WFproj.  This is the exact "S2412 curve = S1550 F-side curve"
statement, with no choice of an algebraic-closure isomorphism. -/
theorem S2440_curve_ident_trans :
    S2411WK (S2440FvCurve T b) = (WFproj T b).toAffine :=
  (S2440_curve_ident T b).trans (S2440_curve_ident_sideF T b)

/-- Transport of affine points along an equality of curves over LF. -/
noncomputable def S2440castPoint {W₁ W₂ : WeierstrassCurve (LF T b)} (h : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  cases h
  exact AddEquiv.refl _

/-- The point-level additive equivalence from the S2412 curve over F_v to the S1550
F-side affine curve, mediated only by the definitional curve identities. -/
noncomputable def S2440affineTransport :
    (S2411WK (S2440FvCurve T b)).toAffine.Point ≃+ (WFproj T b).toAffine.Point :=
  (S2440castPoint T b (S2440_curve_ident T b)).trans
    (S2440castPoint T b (S2440_curve_ident_sideF T b))

/-! ## Characteristic zero: 2 is nonzero on F_v and on LF -/

/-- The completion F_v is a characteristic-zero field, so 2 is nonzero. -/
theorem S2440_two_ne_zero_completion : (2 : Fv T b) ≠ 0 := by
  haveI : CharZero (Fv T b) := inferInstance
  norm_num

/-- The algebraic closure LF is a characteristic-zero field, so 2 is nonzero. -/
theorem S2440_two_ne_zero_closure : (2 : LF T b) ≠ 0 := by
  haveI : CharZero (LF T b) := inferInstance
  norm_num

/-! ## Generic preservation along additive equivalences -/

private theorem s2440_addEquiv_two_nsmul {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) {P : A} (hP : (2 : Nat) • P = 0) : (2 : Nat) • e P = 0 := by
  rw [← map_nsmul, hP, map_zero]

private theorem s2440_addEquiv_ne_zero {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) {P : A} (hP : P ≠ 0) : e P ≠ 0 := by
  intro h
  exact hP (e.injective (by rw [h, map_zero]))

private theorem s2440_addEquiv_ne {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) {P Q : A} (h : P ≠ Q) : e P ≠ e Q :=
  e.injective.ne h

/-! ## The S2412 points on the F-side curve over F_v -/

/-- The affine 2-torsion point attached to a root x of the base-changed 2-division
polynomial on the S2412 curve over F_v, transported to the S1550 F-side affine
curve.  This is the S2354 construction with the actual S2337Y-coordinate, not an
arbitrary point. -/
noncomputable def S2440AffinePoint (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2440FvCurve T b).twoTorsionPolynomial).roots) :
    (WFproj T b).toAffine.Point :=
  S2440affineTransport T b
    (S2354Point (S2411WK (S2440FvCurve T b)) (S2440_two_ne_zero_closure T b) x
      (S2405_eval_zero_of_mem (S2440FvCurve T b) x hx))

/-- The S2412 existential at R = F_v: three 2-torsion points on the S2412 curve
over F_v, exactly as produced by S2412ThreePoints. -/
theorem S2440_S2412_three_points (h2 : (2 : Fv T b) ≠ 0) :
    ∃ P1 P2 P3 : (S2411WK (S2440FvCurve T b)).toAffine.Point,
      (2 : Nat) • P1 = 0 ∧ (2 : Nat) • P2 = 0 ∧ (2 : Nat) • P3 = 0 :=
  S2412ThreePoints (S2440FvCurve T b) h2

/-- The transported S2412 point has order two. -/
theorem S2440AffinePoint_two_nsmul (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2440FvCurve T b).twoTorsionPolynomial).roots) :
    (2 : Nat) • S2440AffinePoint T b x hx = 0 :=
  s2440_addEquiv_two_nsmul (S2440affineTransport T b)
    (S2358_two_nsmul (S2411WK (S2440FvCurve T b)) (S2440_two_ne_zero_closure T b) x
      (S2405_eval_zero_of_mem (S2440FvCurve T b) x hx))

/-- The transported S2412 point is nonzero. -/
theorem S2440AffinePoint_ne_zero (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2440FvCurve T b).twoTorsionPolynomial).roots) :
    S2440AffinePoint T b x hx ≠ 0 :=
  s2440_addEquiv_ne_zero (S2440affineTransport T b)
    (S2414_point_ne_zero (S2440FvCurve T b) (S2440_two_ne_zero_closure T b) x hx)

/-- Distinct roots give distinct transported S2412 points. -/
theorem S2440AffinePoint_ne (x y : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2440FvCurve T b).twoTorsionPolynomial).roots)
    (hy : y ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2440FvCurve T b).twoTorsionPolynomial).roots)
    (hxy : x ≠ y) :
    S2440AffinePoint T b x hx ≠ S2440AffinePoint T b y hy :=
  s2440_addEquiv_ne (S2440affineTransport T b)
    (S2414_point_ne (S2440FvCurve T b) (S2440_two_ne_zero_closure T b) x y hx hy hxy)

/-- The explicit S2412 witnesses are three pairwise distinct roots giving nonzero
2-torsion points on the S2412 curve over F_v. -/
theorem S2440_S2412_three_points_distinct (h2 : (2 : Fv T b) ≠ 0) :
    ∃ x y z : LF T b,
      ∃ hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
        (S2440FvCurve T b).twoTorsionPolynomial).roots,
      ∃ hy : y ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
        (S2440FvCurve T b).twoTorsionPolynomial).roots,
      ∃ hz : z ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
        (S2440FvCurve T b).twoTorsionPolynomial).roots,
        x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        (2 : Nat) • S2354Point (S2411WK (S2440FvCurve T b))
          (S2440_two_ne_zero_closure T b) x
          (S2405_eval_zero_of_mem (S2440FvCurve T b) x hx) = 0 ∧
        (2 : Nat) • S2354Point (S2411WK (S2440FvCurve T b))
          (S2440_two_ne_zero_closure T b) y
          (S2405_eval_zero_of_mem (S2440FvCurve T b) y hy) = 0 ∧
        (2 : Nat) • S2354Point (S2411WK (S2440FvCurve T b))
          (S2440_two_ne_zero_closure T b) z
          (S2405_eval_zero_of_mem (S2440FvCurve T b) z hz) = 0 := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hx, hy, hz⟩ :=
    S2376ThreeDistinctRoots (S2440FvCurve T b) h2
  exact ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz,
    S2358_two_nsmul (S2411WK (S2440FvCurve T b)) (S2440_two_ne_zero_closure T b) x
      (S2405_eval_zero_of_mem (S2440FvCurve T b) x hx),
    S2358_two_nsmul (S2411WK (S2440FvCurve T b)) (S2440_two_ne_zero_closure T b) y
      (S2405_eval_zero_of_mem (S2440FvCurve T b) y hy),
    S2358_two_nsmul (S2411WK (S2440FvCurve T b)) (S2440_two_ne_zero_closure T b) z
      (S2405_eval_zero_of_mem (S2440FvCurve T b) z hz)⟩

/-! ## The F-side projective points of S1550 -/

/-- The S2412 point as a point of the S1550 projective F-side curve. -/
noncomputable def S2440SideFPoint (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2440FvCurve T b).twoTorsionPolynomial).roots) :
    SideFPoint T b :=
  (WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b)).symm
    (S2440AffinePoint T b x hx)

/-- The F-side point has order two. -/
theorem S2440SideFPoint_two_nsmul (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2440FvCurve T b).twoTorsionPolynomial).roots) :
    (2 : Nat) • S2440SideFPoint T b x hx = 0 :=
  s2440_addEquiv_two_nsmul
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b)).symm
    (S2440AffinePoint_two_nsmul T b x hx)

/-- The F-side point is nonzero. -/
theorem S2440SideFPoint_ne_zero (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2440FvCurve T b).twoTorsionPolynomial).roots) :
    S2440SideFPoint T b x hx ≠ 0 :=
  s2440_addEquiv_ne_zero
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b)).symm
    (S2440AffinePoint_ne_zero T b x hx)

/-- Distinct roots give distinct F-side projective points. -/
theorem S2440SideFPoint_ne (x y : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2440FvCurve T b).twoTorsionPolynomial).roots)
    (hy : y ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2440FvCurve T b).twoTorsionPolynomial).roots)
    (hxy : x ≠ y) :
    S2440SideFPoint T b x hx ≠ S2440SideFPoint T b y hy :=
  s2440_addEquiv_ne
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b)).symm
    (S2440AffinePoint_ne T b x y hx hy hxy)

/-- There are three pairwise distinct nonzero points of order two on the S1550
F-side projective curve; each is the toAffineAddEquiv image of an S2412 point. -/
theorem S2440_three_sideF_points (h2 : (2 : Fv T b) ≠ 0) :
    ∃ P1 P2 P3 : SideFPoint T b,
      (2 : Nat) • P1 = 0 ∧ (2 : Nat) • P2 = 0 ∧ (2 : Nat) • P3 = 0 ∧
        P1 ≠ P2 ∧ P1 ≠ P3 ∧ P2 ≠ P3 ∧
        P1 ≠ 0 ∧ P2 ≠ 0 ∧ P3 ≠ 0 := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hx, hy, hz⟩ :=
    S2376ThreeDistinctRoots (S2440FvCurve T b) h2
  exact ⟨S2440SideFPoint T b x hx, S2440SideFPoint T b y hy, S2440SideFPoint T b z hz,
    S2440SideFPoint_two_nsmul T b x hx,
    S2440SideFPoint_two_nsmul T b y hy,
    S2440SideFPoint_two_nsmul T b z hz,
    S2440SideFPoint_ne T b x y hx hy hxy,
    S2440SideFPoint_ne T b x z hx hz hxz,
    S2440SideFPoint_ne T b y z hy hz hyz,
    S2440SideFPoint_ne_zero T b x hx,
    S2440SideFPoint_ne_zero T b y hy,
    S2440SideFPoint_ne_zero T b z hz⟩

/-! ## The K-side points via pointTransport -/

/-- The K-side point: the actual pointTransport image of the S2412 point on the
F-side curve. -/
noncomputable def S2440SideKPoint (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2440FvCurve T b).twoTorsionPolynomial).roots) :
    SideKPoint T b :=
  pointTransport T b (S2440SideFPoint T b x hx)

/-- The K-side point is the pointTransport image of the F-side point: this is the
exact transport identity required by the S1493 point-level comparison. -/
theorem S2440SideKPoint_spec (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2440FvCurve T b).twoTorsionPolynomial).roots) :
    S2440SideKPoint T b x hx =
      pointTransport T b
        ((WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b)).symm
          (S2440AffinePoint T b x hx)) := rfl

/-- The composite additive equivalence from the actual S2412 curve over
AlgebraicClosure F_v to the K-side projective point group: curve identification,
then toAffineAddEquiv, then the actual pointTransport. -/
noncomputable def S2440sideKEquiv :
    (S2411WK (S2440FvCurve T b)).toAffine.Point ≃+ SideKPoint T b :=
  (S2440affineTransport T b).trans
    (((WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b)).symm).trans
      (pointTransport T b))

/-- Applying the composite transport is the same as applying pointTransport to the
toAffineAddEquiv image of the S2412 point. -/
theorem S2440sideKEquiv_apply (P : (S2411WK (S2440FvCurve T b)).toAffine.Point) :
    S2440sideKEquiv T b P =
      pointTransport T b
        ((WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b)).symm
          (S2440affineTransport T b P)) := by
  rfl

/-- Applying the composite transport to the actual S2354 construction gives the
K-side point S2440SideKPoint. -/
theorem S2440SideKPoint_eq_sideKEquiv (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2440FvCurve T b).twoTorsionPolynomial).roots) :
    S2440SideKPoint T b x hx =
      S2440sideKEquiv T b
        (S2354Point (S2411WK (S2440FvCurve T b)) (S2440_two_ne_zero_closure T b) x
          (S2405_eval_zero_of_mem (S2440FvCurve T b) x hx)) := by
  rfl

/-- The K-side point has order two. -/
theorem S2440SideKPoint_two_nsmul (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2440FvCurve T b).twoTorsionPolynomial).roots) :
    (2 : Nat) • S2440SideKPoint T b x hx = 0 :=
  s2440_addEquiv_two_nsmul (pointTransport T b)
    (S2440SideFPoint_two_nsmul T b x hx)

/-- The K-side point is nonzero. -/
theorem S2440SideKPoint_ne_zero (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2440FvCurve T b).twoTorsionPolynomial).roots) :
    S2440SideKPoint T b x hx ≠ 0 :=
  s2440_addEquiv_ne_zero (pointTransport T b)
    (S2440SideFPoint_ne_zero T b x hx)

/-- Distinct roots give distinct K-side points. -/
theorem S2440SideKPoint_ne (x y : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2440FvCurve T b).twoTorsionPolynomial).roots)
    (hy : y ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2440FvCurve T b).twoTorsionPolynomial).roots)
    (hxy : x ≠ y) :
    S2440SideKPoint T b x hx ≠ S2440SideKPoint T b y hy :=
  s2440_addEquiv_ne (pointTransport T b) (S2440SideFPoint_ne T b x y hx hy hxy)

/-- The S2412 existential itself, transported: the three 2-torsion points produced
by S2412ThreePoints at R = F_v map, under the composite transport, to three K-side
2-torsion points.  No point is chosen by hand. -/
theorem S2440_S2412_transport (h2 : (2 : Fv T b) ≠ 0) :
    ∃ Q1 Q2 Q3 : SideKPoint T b,
      (2 : Nat) • Q1 = 0 ∧ (2 : Nat) • Q2 = 0 ∧ (2 : Nat) • Q3 = 0 := by
  obtain ⟨P1, P2, P3, hP1, hP2, hP3⟩ := S2440_S2412_three_points T b h2
  exact ⟨S2440sideKEquiv T b P1, S2440sideKEquiv T b P2, S2440sideKEquiv T b P3,
    s2440_addEquiv_two_nsmul (S2440sideKEquiv T b) hP1,
    s2440_addEquiv_two_nsmul (S2440sideKEquiv T b) hP2,
    s2440_addEquiv_two_nsmul (S2440sideKEquiv T b) hP3⟩

/-! ## The three K-side 2-torsion points -/

/-- There are three pairwise distinct nonzero SideKPoint points of order two, each
the actual pointTransport image of an S2412 point on the S1550 F-side curve. -/
theorem S2440_three_sideK_points (h2 : (2 : Fv T b) ≠ 0) :
    ∃ P1 P2 P3 : SideKPoint T b,
      (2 : Nat) • P1 = 0 ∧ (2 : Nat) • P2 = 0 ∧ (2 : Nat) • P3 = 0 ∧
        P1 ≠ P2 ∧ P1 ≠ P3 ∧ P2 ≠ P3 ∧
        P1 ≠ 0 ∧ P2 ≠ 0 ∧ P3 ≠ 0 := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hx, hy, hz⟩ :=
    S2376ThreeDistinctRoots (S2440FvCurve T b) h2
  exact ⟨S2440SideKPoint T b x hx, S2440SideKPoint T b y hy, S2440SideKPoint T b z hz,
    S2440SideKPoint_two_nsmul T b x hx,
    S2440SideKPoint_two_nsmul T b y hy,
    S2440SideKPoint_two_nsmul T b z hz,
    S2440SideKPoint_ne T b x y hx hy hxy,
    S2440SideKPoint_ne T b x z hx hz hxz,
    S2440SideKPoint_ne T b y z hy hz hyz,
    S2440SideKPoint_ne_zero T b x hx,
    S2440SideKPoint_ne_zero T b y hy,
    S2440SideKPoint_ne_zero T b z hz⟩

/-! ## The exact interface that is not constructed (and not needed)

The construction above is complete for the S2412/S2414 points, because S2412 is
instantiated at R = F_v, so that AlgebraicClosure R is literally LF and
S2440_curve_ident is rfl.  A route starting from the 2-torsion points of the
*global* arithmetic curve over AlgebraicClosure T.arithmetic.F would instead need
the following point-level object.  It is recorded here verbatim, but no inhabitant
is constructed and no theorem depends on it. -/

/-- The exact point-level global-closure interface: a ring map from the algebraic
closure of the global field T.arithmetic.F to LF, compatible with the two
structural maps from T.arithmetic.F (the direct one and the one through F_v).
No inhabitant is constructed in this file. -/
structure S2440GlobalClosureMap where
  toRingHom : AlgebraicClosure T.arithmetic.F →+* LF T b
  commutes : ∀ x : T.arithmetic.F,
    toRingHom (algebraMap T.arithmetic.F (AlgebraicClosure T.arithmetic.F) x) =
      algebraMap (Fv T b) (LF T b) (algebraMap T.arithmetic.F (Fv T b) x)

/-- The proposition asserting existence of the global point-level closure map.  It
is recorded as the exact missing interface of the "global" S2412 route; it is not
proved and nothing in this file uses it.  The route actually taken (S2412 at
R = F_v) needs no such map. -/
def S2440MissingGlobalClosureMap : Prop :=
  Nonempty (S2440GlobalClosureMap T b)

#check S2440_curve_ident
#check S2440_curve_ident_trans
#check S2440_S2412_transport
#check S2440_three_sideF_points
#check S2440_three_sideK_points

#print axioms S2440_curve_ident
#print axioms S2440_S2412_three_points
#print axioms S2440_S2412_transport
#print axioms S2440_three_sideK_points

end LeanFormal.IUT.XiFPaper.S2440S1493PointTransportActualAdapted

end
