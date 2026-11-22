import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual
import tmp.sheaf.xif.paper.S2414ThreePointsDistinctActual

/-!
# S2436: the S1493 point-level transport of the three F-side 2-torsion points

S2415 recorded the exact missing object of the S1493/S1550 route: the three
2-torsion points produced by S2412 live on `W.map (algebraMap R (AlgebraicClosure R))`,
while the S1550 F-side curve is the base change of the F-side curve to
`LF = AlgebraicClosure F_v`; the required identification had not been constructed.
This file constructs it, with no `sorry`, no axiom and no non-canonical choice.

## The identification

`S2412ThreePoints` is stated for an arbitrary field `R` and curve `W` over `R`.
The F-side curve of S1550 is by definition the base change of `T.arithmetic.curve`
along `F -> F_v` and then along `F_v -> LF`.  Taking
`R := F_v = Completion (sectionFPlace T b)` and
`W := S2436FvCurve = (T.arithmetic.curve.baseChange F_v).curve`, the S2412 curve
`S2411WK W = W.map (algebraMap F_v (AlgebraicClosure F_v))` is *definitionally* the
affine curve underlying the S1550 projective F-side curve `WFproj` (both are
`T.arithmetic.curve` mapped along `F -> F_v -> LF`).  This is
`S2436_curve_ident` and `S2436_curve_ident_sideF`, and it is a `rfl`-identity:
no choice of an algebraic-closure isomorphism enters.

## What is constructed

* `S2436AffinePoint` is the S2412/S2354 2-torsion point attached to a root of the
  base-changed 2-division polynomial, transported along the curve identity to the
  S1550 F-side affine curve.
* `S2436SideFPoint` is its image in `SideFPoint T b` under
  `Projective.Point.toAffineAddEquiv (WFproj T b)`.
* `S2436SideKPoint = pointTransport T b (S2436SideFPoint ...)` is the K-side point.
* `S2436SideKPoint_two_nsmul`, `S2436SideKPoint_ne_zero` and
  `S2436SideKPoint_ne` prove that `2 • P = 0`, that the points are nonzero, and
  that they are pairwise distinct; each property is preserved along the additive
  equivalences `S2436affineTransport`, `toAffineAddEquiv` and `pointTransport`.
* `S2436_three_sideK_points` combines them: three pairwise distinct nonzero
  K-side points of order two.

## Boundary

No point-level map `AlgebraicClosure F -> LF` over `F` is constructed or needed.
The current API has no `Algebra.IsAlgebraic T.arithmetic.F (Fv T b)` instance, so
`IsAlgClosure.equivOfAlgebraic` does not apply to `AlgebraicClosure F` and `LF`,
and `IsAlgClosed.lift` would give only a non-canonical embedding.  The canonical
statement is the one used here: the F-side curve over `LF` *is* the base change of
the curve over `F_v`, and S2412 is instantiated there.  This file replaces the
bare `#check`-only placeholder `S2415SideKPointActual`.
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
open LeanFormal.IUT.XiFPaper.S2414ThreePointsDistinctActual
open LeanFormal.IUT.XiFPaper.S2412ThreePointsTransportActual

namespace LeanFormal.IUT.XiFPaper.S2436S1493PointTransportActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- `LF = AlgebraicClosure F_v` is a field, hence has decidable equality; this is
the instance the affine point group law of Mathlib requires. -/
local instance s2436DecEqLF : DecidableEq (AlgebraicClosure (Fv T b)) := Classical.decEq _

/-! ## The S2412 input curve over `F_v` and its identification with the S1550 curve -/

/-- The F-side curve base changed to the F-completion `F_v`: the Weierstrass curve
over `F_v` on which the S2412 construction is run. -/
abbrev S2436FvCurve : WeierstrassCurve (Fv T b) :=
  (T.arithmetic.curve.baseChange (Fv T b)).curve

/-- The S2412 input curve, base changed to the algebraic closure `LF`, is the base
change of `S2436FvCurve` to `LF`.  This is the point-level identification of the
S2412 curve with the F-side curve of S1550; it is definitional. -/
theorem S2436_curve_ident :
    S2411WK (S2436FvCurve T b) = (S2436FvCurve T b).baseChange (LF T b) := rfl

/-- The base change of `S2436FvCurve` to `LF` is the affine curve underlying the
S1550 F-side projective curve `WFproj`. -/
theorem S2436_curve_ident_sideF :
    (S2436FvCurve T b).baseChange (LF T b) = (WFproj T b).toAffine := rfl

/-- Transport of affine points along an equality of curves over `LF`. -/
noncomputable def S2436castPoint {W₁ W₂ : WeierstrassCurve (LF T b)} (h : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  cases h
  exact AddEquiv.refl _

/-- The point-level additive equivalence from the S2412 curve over `F_v` to the
S1550 F-side affine curve.  It is the identity on points, mediated only by the
definitional curve identities above. -/
noncomputable def S2436affineTransport :
    (S2411WK (S2436FvCurve T b)).toAffine.Point ≃+ (WFproj T b).toAffine.Point :=
  (S2436castPoint T b (S2436_curve_ident T b)).trans
    (S2436castPoint T b (S2436_curve_ident_sideF T b))

/-! ## Characteristic zero: `2` is nonzero on `F_v` and on `LF` -/

/-- The completion `F_v` is a characteristic-zero field. -/
theorem S2436_two_ne_zero_completion : (2 : Fv T b) ≠ 0 := by
  norm_num

/-- The algebraic closure `LF` is a characteristic-zero field. -/
theorem S2436_two_ne_zero_closure : (2 : LF T b) ≠ 0 := by
  norm_num

/-! ## Generic preservation along additive equivalences -/

private theorem s2436_addEquiv_two_nsmul {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) {P : A} (hP : (2 : Nat) • P = 0) : (2 : Nat) • e P = 0 := by
  rw [← map_nsmul, hP, map_zero]

private theorem s2436_addEquiv_ne_zero {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) {P : A} (hP : P ≠ 0) : e P ≠ 0 := by
  intro h
  exact hP (e.injective (by rw [h, map_zero]))

private theorem s2436_addEquiv_ne {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) {P Q : A} (h : P ≠ Q) : e P ≠ e Q :=
  e.injective.ne h

/-! ## The S2412 points on the F-side curve over `F_v` -/

/-- The affine 2-torsion point attached to a root `x` of the base-changed
2-division polynomial on the S2412 curve over `F_v`, transported to the S1550
F-side affine curve.  This is the S2354 construction with the actual
`S2337Y`-coordinate, not an arbitrary point. -/
noncomputable def S2436AffinePoint (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2436FvCurve T b).twoTorsionPolynomial).roots) :
    (WFproj T b).toAffine.Point :=
  S2436affineTransport T b
    (S2354Point (S2411WK (S2436FvCurve T b)) (S2436_two_ne_zero_closure T b) x
      (S2405_eval_zero_of_mem (S2436FvCurve T b) x hx))

/-- The S2412 existential at `R = F_v`: three 2-torsion points on the S2412 curve
over `F_v`.  Their explicit witnesses are the points `S2354Point ...` used by
`S2436AffinePoint`; see `S2436_S2412_three_points_distinct`. -/
theorem S2436_S2412_three_points (h2 : (2 : Fv T b) ≠ 0) :
    ∃ P1 P2 P3 : (S2411WK (S2436FvCurve T b)).toAffine.Point,
      (2 : Nat) • P1 = 0 ∧ (2 : Nat) • P2 = 0 ∧ (2 : Nat) • P3 = 0 :=
  S2412ThreePoints (S2436FvCurve T b) h2

/-- The transported S2412 point has order two. -/
theorem S2436AffinePoint_two_nsmul (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2436FvCurve T b).twoTorsionPolynomial).roots) :
    (2 : Nat) • S2436AffinePoint T b x hx = 0 :=
  s2436_addEquiv_two_nsmul (S2436affineTransport T b)
    (S2358_two_nsmul (S2411WK (S2436FvCurve T b)) (S2436_two_ne_zero_closure T b) x
      (S2405_eval_zero_of_mem (S2436FvCurve T b) x hx))

/-- The transported S2412 point is nonzero. -/
theorem S2436AffinePoint_ne_zero (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2436FvCurve T b).twoTorsionPolynomial).roots) :
    S2436AffinePoint T b x hx ≠ 0 :=
  s2436_addEquiv_ne_zero (S2436affineTransport T b)
    (S2414_point_ne_zero (S2436FvCurve T b) (S2436_two_ne_zero_closure T b) x hx)

/-- Distinct roots give distinct transported S2412 points. -/
theorem S2436AffinePoint_ne (x y : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2436FvCurve T b).twoTorsionPolynomial).roots)
    (hy : y ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2436FvCurve T b).twoTorsionPolynomial).roots)
    (hxy : x ≠ y) :
    S2436AffinePoint T b x hx ≠ S2436AffinePoint T b y hy :=
  s2436_addEquiv_ne (S2436affineTransport T b)
    (S2414_point_ne (S2436FvCurve T b) (S2436_two_ne_zero_closure T b) x y hx hy hxy)

/-- The explicit S2412 witnesses are three pairwise distinct nonzero 2-torsion
points on the S2412 curve over `F_v`. -/
theorem S2436_S2412_three_points_distinct (h2 : (2 : Fv T b) ≠ 0) :
    ∃ x y z : LF T b,
      ∃ hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
        (S2436FvCurve T b).twoTorsionPolynomial).roots,
      ∃ hy : y ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
        (S2436FvCurve T b).twoTorsionPolynomial).roots,
      ∃ hz : z ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
        (S2436FvCurve T b).twoTorsionPolynomial).roots,
        x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        (2 : Nat) • S2354Point (S2411WK (S2436FvCurve T b))
          (S2436_two_ne_zero_closure T b) x
          (S2405_eval_zero_of_mem (S2436FvCurve T b) x hx) = 0 ∧
        (2 : Nat) • S2354Point (S2411WK (S2436FvCurve T b))
          (S2436_two_ne_zero_closure T b) y
          (S2405_eval_zero_of_mem (S2436FvCurve T b) y hy) = 0 ∧
        (2 : Nat) • S2354Point (S2411WK (S2436FvCurve T b))
          (S2436_two_ne_zero_closure T b) z
          (S2405_eval_zero_of_mem (S2436FvCurve T b) z hz) = 0 := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hx, hy, hz⟩ :=
    S2376ThreeDistinctRoots (S2436FvCurve T b) h2
  exact ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz,
    S2358_two_nsmul (S2411WK (S2436FvCurve T b)) (S2436_two_ne_zero_closure T b) x
      (S2405_eval_zero_of_mem (S2436FvCurve T b) x hx),
    S2358_two_nsmul (S2411WK (S2436FvCurve T b)) (S2436_two_ne_zero_closure T b) y
      (S2405_eval_zero_of_mem (S2436FvCurve T b) y hy),
    S2358_two_nsmul (S2411WK (S2436FvCurve T b)) (S2436_two_ne_zero_closure T b) z
      (S2405_eval_zero_of_mem (S2436FvCurve T b) z hz)⟩

/-! ## The F-side projective points of S1550 -/

/-- The S2412 point as a point of the S1550 projective F-side curve. -/
noncomputable def S2436SideFPoint (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2436FvCurve T b).twoTorsionPolynomial).roots) :
    SideFPoint T b :=
  (WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b)).symm
    (S2436AffinePoint T b x hx)

/-- The F-side point has order two. -/
theorem S2436SideFPoint_two_nsmul (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2436FvCurve T b).twoTorsionPolynomial).roots) :
    (2 : Nat) • S2436SideFPoint T b x hx = 0 :=
  s2436_addEquiv_two_nsmul
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b)).symm
    (S2436AffinePoint_two_nsmul T b x hx)

/-- The F-side point is nonzero. -/
theorem S2436SideFPoint_ne_zero (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2436FvCurve T b).twoTorsionPolynomial).roots) :
    S2436SideFPoint T b x hx ≠ 0 :=
  s2436_addEquiv_ne_zero
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b)).symm
    (S2436AffinePoint_ne_zero T b x hx)

/-- Distinct roots give distinct F-side projective points. -/
theorem S2436SideFPoint_ne (x y : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2436FvCurve T b).twoTorsionPolynomial).roots)
    (hy : y ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2436FvCurve T b).twoTorsionPolynomial).roots)
    (hxy : x ≠ y) :
    S2436SideFPoint T b x hx ≠ S2436SideFPoint T b y hy :=
  s2436_addEquiv_ne
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b)).symm
    (S2436AffinePoint_ne T b x y hx hy hxy)

/-- There are three pairwise distinct nonzero points of order two on the S1550
F-side projective curve; each is the `toAffineAddEquiv` image of an S2412 point. -/
theorem S2436_three_sideF_points (h2 : (2 : Fv T b) ≠ 0) :
    ∃ P1 P2 P3 : SideFPoint T b,
      (2 : Nat) • P1 = 0 ∧ (2 : Nat) • P2 = 0 ∧ (2 : Nat) • P3 = 0 ∧
        P1 ≠ P2 ∧ P1 ≠ P3 ∧ P2 ≠ P3 ∧
        P1 ≠ 0 ∧ P2 ≠ 0 ∧ P3 ≠ 0 := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hx, hy, hz⟩ :=
    S2376ThreeDistinctRoots (S2436FvCurve T b) h2
  exact ⟨S2436SideFPoint T b x hx, S2436SideFPoint T b y hy, S2436SideFPoint T b z hz,
    S2436SideFPoint_two_nsmul T b x hx,
    S2436SideFPoint_two_nsmul T b y hy,
    S2436SideFPoint_two_nsmul T b z hz,
    S2436SideFPoint_ne T b x y hx hy hxy,
    S2436SideFPoint_ne T b x z hx hz hxz,
    S2436SideFPoint_ne T b y z hy hz hyz,
    S2436SideFPoint_ne_zero T b x hx,
    S2436SideFPoint_ne_zero T b y hy,
    S2436SideFPoint_ne_zero T b z hz⟩

/-! ## The K-side points via `pointTransport` -/

/-- The K-side point: the actual `pointTransport` image of the S2412 point on the
F-side curve. -/
noncomputable def S2436SideKPoint (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2436FvCurve T b).twoTorsionPolynomial).roots) :
    SideKPoint T b :=
  pointTransport T b (S2436SideFPoint T b x hx)

/-- The K-side point is the `pointTransport` image of the F-side point: this is the
exact transport identity required by the S1493 point-level comparison. -/
theorem S2436SideKPoint_spec (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2436FvCurve T b).twoTorsionPolynomial).roots) :
    S2436SideKPoint T b x hx =
      pointTransport T b
        ((WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b)).symm
          (S2436AffinePoint T b x hx)) := rfl

/-- The K-side point has order two. -/
theorem S2436SideKPoint_two_nsmul (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2436FvCurve T b).twoTorsionPolynomial).roots) :
    (2 : Nat) • S2436SideKPoint T b x hx = 0 :=
  s2436_addEquiv_two_nsmul (pointTransport T b)
    (S2436SideFPoint_two_nsmul T b x hx)

/-- The K-side point is nonzero. -/
theorem S2436SideKPoint_ne_zero (x : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2436FvCurve T b).twoTorsionPolynomial).roots) :
    S2436SideKPoint T b x hx ≠ 0 :=
  s2436_addEquiv_ne_zero (pointTransport T b)
    (S2436SideFPoint_ne_zero T b x hx)

/-- Distinct roots give distinct K-side points. -/
theorem S2436SideKPoint_ne (x y : LF T b)
    (hx : x ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2436FvCurve T b).twoTorsionPolynomial).roots)
    (hy : y ∈ (Cubic.map (algebraMap (Fv T b) (AlgebraicClosure (Fv T b)))
      (S2436FvCurve T b).twoTorsionPolynomial).roots)
    (hxy : x ≠ y) :
    S2436SideKPoint T b x hx ≠ S2436SideKPoint T b y hy :=
  s2436_addEquiv_ne (pointTransport T b) (S2436SideFPoint_ne T b x y hx hy hxy)

/-! ## The three K-side 2-torsion points -/

/-- There are three pairwise distinct nonzero `SideKPoint` points of order two,
each the actual `pointTransport` image of an S2412 point on the S1550 F-side
curve. -/
theorem S2436_three_sideK_points (h2 : (2 : Fv T b) ≠ 0) :
    ∃ P1 P2 P3 : SideKPoint T b,
      (2 : Nat) • P1 = 0 ∧ (2 : Nat) • P2 = 0 ∧ (2 : Nat) • P3 = 0 ∧
        P1 ≠ P2 ∧ P1 ≠ P3 ∧ P2 ≠ P3 ∧
        P1 ≠ 0 ∧ P2 ≠ 0 ∧ P3 ≠ 0 := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hx, hy, hz⟩ :=
    S2376ThreeDistinctRoots (S2436FvCurve T b) h2
  exact ⟨S2436SideKPoint T b x hx, S2436SideKPoint T b y hy, S2436SideKPoint T b z hz,
    S2436SideKPoint_two_nsmul T b x hx,
    S2436SideKPoint_two_nsmul T b y hy,
    S2436SideKPoint_two_nsmul T b z hz,
    S2436SideKPoint_ne T b x y hx hy hxy,
    S2436SideKPoint_ne T b x z hx hz hxz,
    S2436SideKPoint_ne T b y z hy hz hyz,
    S2436SideKPoint_ne_zero T b x hx,
    S2436SideKPoint_ne_zero T b y hy,
    S2436SideKPoint_ne_zero T b z hz⟩

#print axioms S2436_curve_ident
#print axioms S2436_S2412_three_points
#print axioms S2436_S2412_three_points_distinct
#print axioms S2436AffinePoint_two_nsmul
#print axioms S2436AffinePoint_ne_zero
#print axioms S2436AffinePoint_ne
#print axioms S2436_three_sideF_points
#print axioms S2436SideKPoint_two_nsmul
#print axioms S2436SideKPoint_ne_zero
#print axioms S2436SideKPoint_ne
#print axioms S2436_three_sideK_points

end LeanFormal.IUT.XiFPaper.S2436S1493PointTransportActual

end
