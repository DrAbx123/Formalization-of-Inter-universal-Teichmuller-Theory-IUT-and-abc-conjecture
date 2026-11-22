import tmp.sheaf.xif.paper.S1537TatePointComparisonActual
import tmp.sheaf.xif.paper.S1493KSideTateTransportActual

/-! # S1550: the actual K-side Tate point comparison from the closure transport

S1493 constructed the actual completion extension Completion (sectionFPlace T b) ->
Completion (sectionKPlace T b), proved it algebraic (completion_isAlgebraic), and
obtained the resulting algebraic-closure equivalence

  sectionClosureEquiv T b :
     AlgebraicClosure (Completion (sectionKPlace T b)) ≃ₐ[Completion (sectionFPlace T b)]
       AlgebraicClosure (Completion (sectionFPlace T b)),

together with sectionClosureEquiv_tateParameterUnit, which carries the K-side Tate
parameter unit to the F-side one.  S1537 recorded the K-side point comparison
TatePointComparison (kSideCurve T) (sectionKPlace T b) (sectionQ T b) as its exact
first missing field.

This file constructs that comparison, with no ambient/proxy comparison and no
Nonempty gate:

* curveEq identifies the affine curve obtained from the F-side base-changed curve
  (T.arithmetic.curve.baseChange F_v).curve at AlgebraicClosure K_v with the
  K-side curve ((kSideCurve T).baseChange K_v).curve.  The identification is the
  actual baseChange_curve_map_eq (S1493) together with the scalar-tower equality of
  the two algebra maps F -> F_v -> K_v^alg and F -> K -> K_v^alg.
* psiAff is the coordinate-level transport of affine points along eFK followed by
  curveEq; affinePointCast is the transport of the affine point group along a
  curve equality.
* pointTransport is the induced additive equivalence on the actual projective
  closure point groups, and pointTransport_galois proves that it intertwines the
  F-side Galois action of tauOf sigma = eKF.symm * sigma * eKF with the K-side
  action of sigma.
* deckEquiv is the quotient equivalence on local units induced by eKF; it sends
  the K-side Tate parameter unit to the F-side one
  (closureUnitEquiv_tateParameterUnit).
* Composing the F-side clause-(b) comparison (sectionTateWitness_comparison) with
  these two equivalences yields the actual K-side comparison tatePointComparison,
  whose galois_naturality field is pointEquiv_galois_naturality.

The last section assembles the actual TateCurveComparison, the S1482 K-side Tate
data, and the S1537 conditional construction from this comparison.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual
open LeanFormal.IUT.XiFPaper.S1482KSideTateUniformizationActual
open LeanFormal.IUT.XiFPaper.S1493KSideTateTransportActual
open LeanFormal.IUT.XiFPaper.S1498KSideTateTransportActual
open LeanFormal.IUT.XiFPaper.S1515KSideTateRealizesCurveActual
open LeanFormal.IUT.XiFPaper.S1537TatePointComparisonActual
open WeierstrassCurve

namespace LeanFormal.IUT.XiFPaper.S1550TatePointComparisonFromClosureActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

abbrev Fv : Type _ := Completion (sectionFPlace T b)
abbrev Kv : Type _ := Completion (sectionKPlace T b)

noncomputable local instance fvKvAlgebra : Algebra (Fv T b) (Kv T b) :=
  (completionMap (k := T.arithmetic.F) (sectionKPlace T b)).toAlgebra

theorem fvKv_scalarTower : IsScalarTower T.arithmetic.F (Fv T b) (Kv T b) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change algebraMap T.arithmetic.F (Kv T b) x = completionMap (k := T.arithmetic.F) (sectionKPlace T b)
      (algebraMap T.arithmetic.F (Fv T b) x)
  exact (S1493KSideTateTransportActual.completionMap_algebraMap_eq (T := T) (b := b) x).symm

noncomputable local instance fvKvScalarTower : IsScalarTower T.arithmetic.F (Fv T b) (Kv T b) :=
  fvKv_scalarTower T b

noncomputable local instance lfDecEq : DecidableEq (AlgebraicClosure (Fv T b)) := Classical.decEq _
noncomputable local instance lkDecEq : DecidableEq (AlgebraicClosure (Kv T b)) := Classical.decEq _

abbrev LF : Type _ := AlgebraicClosure (Fv T b)
abbrev LK : Type _ := AlgebraicClosure (Kv T b)

noncomputable def eKF : LK T b ≃ₐ[Fv T b] LF T b :=
  sectionClosureEquiv (T := T) (b := b)

noncomputable def eFK : LF T b ≃ₐ[Fv T b] LK T b :=
  (eKF T b).symm

abbrev AF : Type _ := WeierstrassCurve.Affine.Point
  ((T.arithmetic.curve.baseChange (Fv T b)).curve.baseChange (LF T b))
abbrev AK : Type _ := WeierstrassCurve.Affine.Point
  ((T.arithmetic.curve.baseChange (Fv T b)).curve.baseChange (LK T b))
abbrev BK : Type _ := WeierstrassCurve.Affine.Point
  (((kSideCurve (T := T)).baseChange (Kv T b)).curve.baseChange (LK T b))

abbrev WFproj : WeierstrassCurve.Projective (LF T b) :=
  ((T.arithmetic.curve.baseChange (Fv T b)).curve.toProjective).baseChange (LF T b)

abbrev WKproj : WeierstrassCurve.Projective (LK T b) :=
  (((kSideCurve (T := T)).baseChange (Kv T b)).curve.toProjective).baseChange (LK T b)

abbrev SideFPoint : Type _ := WeierstrassCurve.Projective.Point (WFproj T b)
abbrev SideKPoint : Type _ := WeierstrassCurve.Projective.Point (WKproj T b)

theorem curveEq : (T.arithmetic.curve.baseChange (Fv T b)).curve.baseChange (LK T b) =
    ((kSideCurve (T := T)).baseChange (Kv T b)).curve.baseChange (LK T b) := by
  have hmap := congrArg (fun W : WeierstrassCurve (Kv T b) =>
      W.map (algebraMap (Kv T b) (LK T b))) (S1493KSideTateTransportActual.baseChange_curve_map_eq (T := T) (b := b))
  let f : (Fv T b) →+* (LK T b) :=
    (algebraMap (Kv T b) (LK T b)).comp (completionMap (k := T.arithmetic.F) (sectionKPlace T b))
  have hcomp : (algebraMap (Fv T b) (LK T b)) = f := by
    ext x
    exact IsScalarTower.algebraMap_apply (Fv T b) (Kv T b) (LK T b) x
  have hmap' : ((T.arithmetic.curve.baseChange (Fv T b)).curve.map
        (completionMap (k := T.arithmetic.F) (sectionKPlace T b))).map
        (algebraMap (Kv T b) (LK T b)) =
      (T.arithmetic.curve.baseChange (Fv T b)).curve.map (algebraMap (Fv T b) (LK T b)) := by
    rw [WeierstrassCurve.map_map]
    rw [hcomp]
  exact hmap'.symm.trans hmap

noncomputable def affinePointCast {W1 W2 : WeierstrassCurve (LK T b)} (h : W1 = W2) :
    WeierstrassCurve.Affine.Point W1 ≃+ WeierstrassCurve.Affine.Point W2 := by
  cases h
  exact AddEquiv.refl _

lemma affinePointCast_zero {W1 W2 : WeierstrassCurve (LK T b)} (h : W1 = W2) :
    affinePointCast (T := T) (b := b) h (0 : WeierstrassCurve.Affine.Point W1) = 0 := by
  cases h
  rfl

lemma affinePointCast_some {W1 W2 : WeierstrassCurve (LK T b)} (h : W1 = W2)
    {x y : LK T b} (hp : WeierstrassCurve.Affine.Nonsingular W1 x y) :
    affinePointCast (T := T) (b := b) h (WeierstrassCurve.Affine.Point.some x y hp) =
      WeierstrassCurve.Affine.Point.some x y (h ▸ hp) := by
  cases h
  rfl

noncomputable def psiAff (P : AF T b) : BK T b :=
  match P with
  | 0 => 0
  | WeierstrassCurve.Affine.Point.some x y hp =>
      WeierstrassCurve.Affine.Point.some ((eFK T b) x) ((eFK T b) y)
        (curveEq T b ▸ (WeierstrassCurve.Affine.baseChange_nonsingular
          (W := (T.arithmetic.curve.baseChange (Fv T b)).curve)
          (f := (eFK T b).toAlgHom) (eFK T b).injective x y).mpr hp)

lemma psiAff_zero : psiAff T b (0 : AF T b) = 0 := rfl

lemma psiAff_some {x y : LF T b}
    (hp : WeierstrassCurve.Affine.Nonsingular
      ((T.arithmetic.curve.baseChange (Fv T b)).curve.baseChange (LF T b)) x y) :
    psiAff T b (WeierstrassCurve.Affine.Point.some x y hp) =
      WeierstrassCurve.Affine.Point.some ((eFK T b) x) ((eFK T b) y)
        (curveEq T b ▸ (WeierstrassCurve.Affine.baseChange_nonsingular
          (W := (T.arithmetic.curve.baseChange (Fv T b)).curve)
          (f := (eFK T b).toAlgHom) (eFK T b).injective x y).mpr hp) := rfl

noncomputable def affinePointMapEquiv
    (e : LF T b ≃ₐ[Fv T b] LK T b) :
    AF T b ≃+ AK T b := by
  refine
    { toFun := WeierstrassCurve.Affine.Point.map
        (W' := (T.arithmetic.curve.baseChange (Fv T b)).curve) e.toAlgHom
      invFun := WeierstrassCurve.Affine.Point.map
        (W' := (T.arithmetic.curve.baseChange (Fv T b)).curve) e.symm.toAlgHom
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_ }
  · intro P
    rw [WeierstrassCurve.Affine.Point.map_map]
    have hcomp : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id (Fv T b) (LF T b) := by
      ext x
      exact e.symm_apply_apply x
    rw [hcomp]
    exact WeierstrassCurve.Affine.Point.map_id P
  · intro P
    rw [WeierstrassCurve.Affine.Point.map_map]
    have hcomp : e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id (Fv T b) (LK T b) := by
      ext x
      exact e.apply_symm_apply x
    rw [hcomp]
    exact WeierstrassCurve.Affine.Point.map_id P
  · intro P Q
    exact map_add (WeierstrassCurve.Affine.Point.map
      (W' := (T.arithmetic.curve.baseChange (Fv T b)).curve) e.toAlgHom) P Q

noncomputable def psiAddEquiv : AF T b ≃+ BK T b :=
  (affinePointMapEquiv (T := T) (b := b) (eFK T b)).trans
    (affinePointCast (T := T) (b := b) (curveEq T b))

lemma psiAff_eq_comp (P : AF T b) :
    psiAff T b P = affinePointCast (T := T) (b := b) (curveEq T b)
      (WeierstrassCurve.Affine.Point.map
        (W' := (T.arithmetic.curve.baseChange (Fv T b)).curve) (eFK T b).toAlgHom P) := by
  cases P with
  | zero =>
      change psiAff T b (0 : AF T b) =
        affinePointCast (T := T) (b := b) (curveEq T b)
          ((WeierstrassCurve.Affine.Point.map
            (W' := (T.arithmetic.curve.baseChange (Fv T b)).curve) (eFK T b).toAlgHom)
            (0 : AF T b))
      rw [psiAff_zero, WeierstrassCurve.Affine.Point.map_zero]
      exact (affinePointCast_zero (T := T) (b := b) (curveEq T b)).symm
  | some x y hp =>
      rw [psiAff_some, WeierstrassCurve.Affine.Point.map_some,
        affinePointCast_some]
      rfl

lemma psiAff_eq_psiAddEquiv (P : AF T b) : psiAff T b P = psiAddEquiv T b P := by
  rw [psiAff_eq_comp]
  rfl

lemma psiAff_galois (sigma : LK T b ≃ₐ[Kv T b] LK T b)
    (P : AF T b) :
    psiAff T b (WeierstrassCurve.Affine.Point.map
        (W' := (T.arithmetic.curve.baseChange (Fv T b)).curve)
        ((eKF T b).symm.trans ((sigma.restrictScalars (Fv T b)).trans (eKF T b))).toAlgHom P) =
      WeierstrassCurve.Affine.Point.map
        (W' := ((kSideCurve (T := T)).baseChange (Kv T b)).curve) sigma.toAlgHom
        (psiAff T b P) := by
  cases P with
  | zero =>
      change psiAff T b ((WeierstrassCurve.Affine.Point.map
        (W' := (T.arithmetic.curve.baseChange (Fv T b)).curve)
        ((eKF T b).symm.trans ((sigma.restrictScalars (Fv T b)).trans (eKF T b))).toAlgHom)
        (0 : AF T b)) =
        (WeierstrassCurve.Affine.Point.map
          (W' := ((kSideCurve (T := T)).baseChange (Kv T b)).curve) sigma.toAlgHom)
          (0 : BK T b)
      rw [WeierstrassCurve.Affine.Point.map_zero, psiAff_zero,
        WeierstrassCurve.Affine.Point.map_zero]
  | some x y hp =>
      rw [WeierstrassCurve.Affine.Point.map_some, psiAff_some, psiAff_some,
        WeierstrassCurve.Affine.Point.map_some]
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      constructor
      · have htau : ((eKF T b).symm.trans ((sigma.restrictScalars (Fv T b)).trans (eKF T b))) x
            = (eKF T b) (sigma ((eKF T b).symm x)) := by
          simp [AlgEquiv.trans_apply]
        change (eFK T b) (((eKF T b).symm.trans ((sigma.restrictScalars (Fv T b)).trans (eKF T b))) x)
          = sigma ((eFK T b) x)
        rw [htau]
        change (eKF T b).symm ((eKF T b) (sigma ((eKF T b).symm x))) = sigma ((eKF T b).symm x)
        rw [AlgEquiv.symm_apply_apply]
      · have htau : ((eKF T b).symm.trans ((sigma.restrictScalars (Fv T b)).trans (eKF T b))) y
            = (eKF T b) (sigma ((eKF T b).symm y)) := by
          simp [AlgEquiv.trans_apply]
        change (eFK T b) (((eKF T b).symm.trans ((sigma.restrictScalars (Fv T b)).trans (eKF T b))) y)
          = sigma ((eFK T b) y)
        rw [htau]
        change (eKF T b).symm ((eKF T b) (sigma ((eKF T b).symm y))) = sigma ((eKF T b).symm y)
        rw [AlgEquiv.symm_apply_apply]

noncomputable def pointTransport : SideFPoint T b ≃+ SideKPoint T b :=
  (WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b)).trans
    ((psiAddEquiv T b).trans
      (WeierstrassCurve.Projective.Point.toAffineAddEquiv (WKproj T b)).symm)

lemma toAffine_pointTransport (P : SideFPoint T b) :
    WeierstrassCurve.Projective.Point.toAffineAddEquiv (WKproj T b) (pointTransport T b P) =
      psiAff T b (WeierstrassCurve.Projective.Point.toAffineAddEquiv (WFproj T b) P) := by
  rw [pointTransport]
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  exact (psiAff_eq_psiAddEquiv T b _).symm

lemma pointTransport_galois (sigma : LK T b ≃ₐ[Kv T b] LK T b)
    (P : SideFPoint T b) :
    pointTransport T b
        (PuncturedEllipticCurve.galoisActionOnPoint
          (T.arithmetic.curve.baseChange (Fv T b))
          ((eKF T b).symm.trans ((sigma.restrictScalars (Fv T b)).trans (eKF T b))) P) =
      PuncturedEllipticCurve.galoisActionOnPoint
        ((kSideCurve (T := T)).baseChange (Kv T b)) sigma (pointTransport T b P) := by
  apply (WeierstrassCurve.Projective.Point.toAffineAddEquiv (WKproj T b)).injective
  rw [toAffine_pointTransport]
  rw [PuncturedEllipticCurve.galoisActionOnPoint,
    PuncturedEllipticCurve.galoisActionOnPoint]
  simp only [AddEquiv.coe_toAddMonoidHom, AddMonoidHom.comp_apply,
    AddEquiv.apply_symm_apply]
  rw [toAffine_pointTransport]
  exact psiAff_galois T b sigma (WeierstrassCurve.Projective.Point.toAffineAddEquiv
    (WFproj T b) P)

/-! ## Unit quotient and full point comparison -/

noncomputable def closureUnitEquiv : (LK T b)ˣ ≃* (LF T b)ˣ :=
  Units.mapEquiv (eKF T b).toRingEquiv.toMulEquiv

lemma closureUnitEquiv_tateParameterUnit :
    (closureUnitEquiv T b).toMonoidHom
        (tateParameterUnit (sectionKPlace T b) (sectionQ T b).q (sectionQ T b).q_ne_zero) =
      tateParameterUnit (sectionFPlace T b) (sectionFQ T b).q (sectionFQ T b).q_ne_zero := by
  change Units.map (eKF T b).toRingEquiv.toMonoidHom
    (tateParameterUnit (sectionKPlace T b) (sectionQ T b).q (sectionQ T b).q_ne_zero) = _
  exact sectionClosureEquiv_tateParameterUnit (T := T) (b := b)

theorem deckSubgroup_map :
    Subgroup.map (closureUnitEquiv T b).toMonoidHom
      (Subgroup.zpowers
        (tateParameterUnit (sectionKPlace T b) (sectionQ T b).q (sectionQ T b).q_ne_zero)) =
      Subgroup.zpowers
        (tateParameterUnit (sectionFPlace T b) (sectionFQ T b).q (sectionFQ T b).q_ne_zero) := by
  rw [MonoidHom.map_zpowers, closureUnitEquiv_tateParameterUnit]

abbrev DeckK : Type _ := ((LK T b)ˣ ⧸ Subgroup.zpowers
  (tateParameterUnit (sectionKPlace T b) (sectionQ T b).q (sectionQ T b).q_ne_zero))

abbrev DeckF : Type _ := ((LF T b)ˣ ⧸ Subgroup.zpowers
  (tateParameterUnit (sectionFPlace T b) (sectionFQ T b).q (sectionFQ T b).q_ne_zero))

noncomputable def deckEquiv : DeckK T b ≃* DeckF T b :=
  QuotientGroup.congr _ _ (closureUnitEquiv T b) (deckSubgroup_map T b)

lemma deckEquiv_mk (u : (LK T b)ˣ) :
    deckEquiv T b (QuotientGroup.mk u) = QuotientGroup.mk (closureUnitEquiv T b u) :=
  QuotientGroup.congr_mk _ _ _ _ u

noncomputable def tauOf (sigma : LK T b ≃ₐ[Kv T b] LK T b) : LF T b ≃ₐ[Fv T b] LF T b :=
  (eKF T b).symm.trans ((sigma.restrictScalars (Fv T b)).trans (eKF T b))

lemma closureUnitEquiv_units_map (sigma : LK T b ≃ₐ[Kv T b] LK T b) (x : (LK T b)ˣ) :
    closureUnitEquiv T b (Units.map sigma.toRingEquiv.toMonoidHom x) =
      Units.map (tauOf T b sigma).toRingEquiv.toMonoidHom (closureUnitEquiv T b x) := by
  apply Units.ext
  change (eKF T b) (sigma (x : LK T b)) = (tauOf T b sigma) ((eKF T b) (x : LK T b))
  simp [tauOf, AlgEquiv.trans_apply]

noncomputable def pointEquiv :
    DeckK T b ≃* Multiplicative (SideKPoint T b) :=
  (deckEquiv T b).trans
    ((sectionTateWitness_comparison T b).points.pointEquiv.trans
      (AddEquiv.toMultiplicative (pointTransport T b)))

lemma pointEquiv_mk (u : (LK T b)ˣ) :
    pointEquiv T b (QuotientGroup.mk u) =
      Multiplicative.ofAdd (pointTransport T b
        ((sectionTateWitness_comparison T b).points.pointEquiv
          (QuotientGroup.mk (closureUnitEquiv T b u))).toAdd) := by
  rw [pointEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply, deckEquiv_mk]
  rfl

theorem pointEquiv_galois_naturality (sigma : LK T b ≃ₐ[Kv T b] LK T b)
    (x : (LK T b)ˣ) :
    pointEquiv T b (QuotientGroup.mk (Units.map sigma.toRingEquiv.toMonoidHom x)) =
      Multiplicative.ofAdd
        (PuncturedEllipticCurve.galoisActionOnPoint
          ((kSideCurve (T := T)).baseChange (Kv T b)) sigma
          ((pointEquiv T b (QuotientGroup.mk x)).toAdd)) := by
  rw [pointEquiv_mk (T := T) (b := b) (Units.map sigma.toRingEquiv.toMonoidHom x)]
  rw [closureUnitEquiv_units_map]
  rw [(sectionTateWitness_comparison T b).points.galois_naturality
    (tauOf T b sigma) (closureUnitEquiv T b x)]
  rw [pointEquiv_mk]
  exact congrArg Multiplicative.ofAdd (pointTransport_galois T b sigma
    ((sectionTateWitness_comparison T b).points.pointEquiv
      (QuotientGroup.mk (closureUnitEquiv T b x))).toAdd)

noncomputable def tatePointComparison :
    TatePointComparison (kSideCurve (T := T)) (sectionKPlace T b) (sectionQ T b) where
  pointEquiv := pointEquiv T b
  galois_naturality := pointEquiv_galois_naturality T b


/-! ## The actual K-side comparison and its consumers -/

/-- The actual K-side TateCurveComparison, assembled from the S1515 coordinate
change/curve realization and the point comparison constructed above. -/
noncomputable def tateCurveComparison :
    TateCurveComparison (kSideCurve (T := T)) (sectionKPlace T b) (sectionQ T b) where
  canonicalIsElliptic := canonicalIsElliptic (T := T) (b := b)
  coordinateChange := s1498CoordinateChange (T := T) (b := b)
  realizesCurve := s1498RealizesCurveTarget (T := T) (b := b)
  points := tatePointComparison T b

/-- The exact K-side first missing comparison of S1537 is now constructed. -/
theorem s1537KPointComparison_nonempty :
    Nonempty (S1537KPointComparison T b) :=
  ⟨tatePointComparison T b⟩

/-- The actual S1482 K-side Tate data, with the point field supplied by the
closure transport. -/
noncomputable def s1482KSideTateData : S1482KSideTateData T b :=
  s1537S1482KSideTateData (T := T) (b := b) (tatePointComparison T b)

end LeanFormal.IUT.XiFPaper.S1550TatePointComparisonFromClosureActual

end