import tmp.sheaf.xif.paper.S1625AddXYZSmulEvalActual
import tmp.sheaf.xif.paper.S1598PolyToFieldCCActual

/-!
# S1626: the addition identity over the universal field, and the evaluation port

This file ports the remaining TauCeti material from
`tmp/TauCeti/TauCeti/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/ZSMul.lean`:

* the universal-field addition identity `addXYZ_smulField` (TauCeti lines 870--905);
* the universal-ring specialisation `ringEval` and the coefficient map `specialize`;
* the ring-level doubling and addition identities, obtained from the field versions
  through injectivity of the fraction-field inclusion;
* the evaluated triple `smulEval` and its specialisation law `ringEval_comp_smulRing`;
* the evaluated doubling and addition laws `dblXYZ_smulEval` and `addXYZ_smulEval`;
* the headline `zsmul_point_eq_smulEval`.

The local hypotheses and names are those of the S1593/S1619/S1622/S1623/S1624/S1625 layer.
No statement is imported as an axiom and no proof uses `sorry`.
-/
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Jacobian
open scoped Polynomial.Bivariate
namespace LeanFormal.IUT.XiFPaper.S1626AddXYZSmulEvalPortActual
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1622ZSMulInductionStepActual
open LeanFormal.IUT.XiFPaper.S1623ZSMulEvalActual
open LeanFormal.IUT.XiFPaper.S1624ZSMulEvalFinalActual
open LeanFormal.IUT.XiFPaper.S1625AddXYZSmulEvalActual
open LeanFormal.IUT.XiFPaper.S1619UniversalPointLayerActual

/-- The universal curve base-changed to the universal coordinate ring. -/
def s1626CurveRing : WeierstrassCurve Universal.Ring := Universal.curve.baseChange Universal.Ring

/-- The universal division-polynomial triple over the universal ring. -/
def smulRing (n : ℤ) : Fin 3 → Universal.Ring :=
  AdjoinRoot.mk Universal.curve.toAffine.polynomial ∘ Universal.smulPoly n

theorem s1626AlgebraMap_comp_smulRing (n : ℤ) :
    (algebraMap Universal.Ring Universal.Field) ∘ smulRing n = smulField n := by
  funext i
  rfl

/-- The coefficient specialization from the universal polynomial ring to a curve `W`. -/
noncomputable def s1626Specialize {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    MvPolynomial Coeff ℤ →+* R :=
  (MvPolynomial.aeval (Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆)).toRingHom

@[simp]
theorem s1626Specialize_X {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (i : Coeff) :
    s1626Specialize W (MvPolynomial.X i) =
      Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ i := by
  simp [s1626Specialize]

theorem s1626Map_specialize {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    Universal.curve.map (s1626Specialize W) = W := by
  ext <;> simp [s1626Specialize, Universal.curve]

/-- Evaluation of universal bivariate polynomials at an affine point. -/
noncomputable def s1626PolyEval {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    Universal.Poly →+* R :=
  eval₂RingHom (eval₂RingHom (s1626Specialize W) x) y

theorem s1626PolyEval_apply {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R)
    (p : Universal.Poly) :
    s1626PolyEval W x y p =
      (p.map (mapRingHom (s1626Specialize W))).evalEval x y :=
  eval₂_eval₂RingHom_apply _ _ _ _

theorem s1626EvalEval_φ {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) (n : ℤ) :
    (W.φ n).evalEval x y = s1626PolyEval W x y (Universal.curve.φ n) := by
  rw [s1626PolyEval_apply,
    ← WeierstrassCurve.map_φ (W := Universal.curve) (f := s1626Specialize W) n,
    s1626Map_specialize]

theorem s1626EvalEval_ψ {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) (n : ℤ) :
    (W.ψ n).evalEval x y = s1626PolyEval W x y (Universal.curve.ψ n) := by
  rw [s1626PolyEval_apply,
    ← WeierstrassCurve.map_ψ (W := Universal.curve) (f := s1626Specialize W) n,
    s1626Map_specialize]

theorem s1626EvalEval_ω {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) (n : ℤ) :
    (W.ω n).evalEval x y = s1626PolyEval W x y (Universal.curve.ω n) := by
  rw [s1626PolyEval_apply,
    ← WeierstrassCurve.map_ω (W := Universal.curve) (f := s1626Specialize W) n,
    s1626Map_specialize]

/-- The ring homomorphism from the universal coordinate ring induced by an affine point. -/
noncomputable def s1626RingEval {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (eqn : W.toAffine.Equation x y) : Universal.Ring →+* R :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (s1626Specialize W) x) y (by
    change s1626PolyEval W x y Universal.curve.toAffine.polynomial = 0
    have hpoly : s1626PolyEval W x y Universal.curve.toAffine.polynomial =
        W.toAffine.polynomial.evalEval x y := by
      rw [s1626PolyEval_apply,
        ← WeierstrassCurve.Affine.map_polynomial (W := Universal.curve)
          (f := s1626Specialize W)]
      change (Universal.curve.map (s1626Specialize W)).toAffine.polynomial.evalEval x y =
        W.toAffine.polynomial.evalEval x y
      rw [s1626Map_specialize]
    rw [hpoly]
    exact eqn)

theorem s1626RingEval_mk {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (eqn : W.toAffine.Equation x y) (p : Universal.Poly) :
    s1626RingEval W eqn (AdjoinRoot.mk Universal.curve.toAffine.polynomial p) =
      s1626PolyEval W x y p := by
  rw [s1626RingEval]
  exact AdjoinRoot.lift_mk _ p

theorem s1626RingEval_algebraMap {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (eqn : W.toAffine.Equation x y) (a : MvPolynomial Coeff ℤ) :
    s1626RingEval W eqn (algebraMap (MvPolynomial Coeff ℤ) Universal.Ring a) =
      s1626Specialize W a := by
  rw [show algebraMap (MvPolynomial Coeff ℤ) Universal.Ring a =
      AdjoinRoot.mk Universal.curve.toAffine.polynomial
        (Polynomial.C (Polynomial.C a)) from ?_]
  · rw [s1626RingEval_mk]
    simp [s1626PolyEval]
  · rw [IsScalarTower.algebraMap_apply (MvPolynomial Coeff ℤ)
      (Polynomial (MvPolynomial Coeff ℤ)) Universal.Ring]
    rw [AdjoinRoot.algebraMap_eq]
    rfl

theorem s1626Map_ringEval {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (eqn : W.toAffine.Equation x y) :
    s1626CurveRing.map (s1626RingEval W eqn) = W := by
  ext <;>
    simp [WeierstrassCurve.map, s1626CurveRing, s1626RingEval_algebraMap,
      s1626Specialize, Universal.curve]

theorem s1626CurveRing_map :
    s1626CurveRing.map (algebraMap Universal.Ring Universal.Field) = pointedCurve := by
  change (Universal.curve.map (algebraMap (MvPolynomial Coeff ℤ) Universal.Ring)).map
      (algebraMap Universal.Ring Universal.Field) = pointedCurve
  rw [WeierstrassCurve.map_map,
    ← IsScalarTower.algebraMap_eq (MvPolynomial Coeff ℤ)
      Universal.Ring Universal.Field,
    pointedCurve, curvePoly, WeierstrassCurve.map_map]
  rfl

theorem s1626JacobianMap_ringEval {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (eqn : W.toAffine.Equation x y) :
    Jacobian.map s1626CurveRing (s1626RingEval W eqn) = W := by
  simpa [Jacobian.map] using s1626Map_ringEval W eqn

/-- The doubling identity over the universal ring. -/
theorem s1626DblXYZ_smulRing (n : ℤ) :
    Jacobian.dblXYZ s1626CurveRing (smulRing n) = smulRing (2 * n) := by
  apply (IsFractionRing.injective Universal.Ring Universal.Field).comp_left
  change (algebraMap Universal.Ring Universal.Field) ∘
      Jacobian.dblXYZ s1626CurveRing (smulRing n) =
    (algebraMap Universal.Ring Universal.Field) ∘ smulRing (2 * n)
  rw [← Jacobian.map_dblXYZ (algebraMap Universal.Ring Universal.Field) (smulRing n)]
  rw [show Jacobian.map s1626CurveRing (algebraMap Universal.Ring Universal.Field) =
      pointedCurve from s1626CurveRing_map,
    s1626AlgebraMap_comp_smulRing n, s1626AlgebraMap_comp_smulRing (2 * n)]
  exact s1624DblXYZ_smulField n


theorem s1626SmulField_zero : smulField 0 = ![1,1,0] := by
  funext i
  fin_cases i <;> simp [smulField, smulPoly, WeierstrassCurve.φ_zero,
    WeierstrassCurve.ω_zero, WeierstrassCurve.ψ_zero]

theorem s1626SmulField_Z (n : ℤ) : smulField n 2 = polyToField (curve.ψ n) := by
  simp [smulField, smulPoly]

theorem s1626Nonsingular_smulField (n : ℤ) :
    pointedCurve.toJacobian.Nonsingular (smulField n) := by
  rcases eq_or_ne n 0 with rfl | h0
  · rw [s1626SmulField_zero]
    exact Jacobian.nonsingular_zero
  · exact s1623NonsingularSmulField n h0

theorem s1626ZSMulPoint_ne_zero (n : ℤ) (h0 : n ≠ 0) :
    n • s1619Point.toJacobian ≠ 0 := by
  intro h
  obtain ⟨hns, hpoint⟩ := s1622ZSMulPointFormula n h0
  have hmap : (n • s1619Point).toJacobian = n • s1619Point.toJacobian := by
    simpa [Affine.Point.toJacobian] using
      (map_zsmul (Jacobian.Point.toAffineAddEquiv (W := pointedCurve)).symm n s1619Point)
  have h0' : n • s1619Point = 0 := by
    apply (Jacobian.Point.toAffineAddEquiv pointedCurve).symm.injective
    change (n • s1619Point).toJacobian = (0 : pointedCurve.toJacobian.Point)
    rw [hmap]
    exact h
  rw [hpoint] at h0'
  exact Affine.Point.some_ne_zero hns h0'

theorem s1626ZSMulPoint_injective :
    Function.Injective (fun n : ℤ => n • s1619Point.toJacobian) := by
  intro m n hmn
  by_contra hne
  have hmn' : m • s1619Point.toJacobian = n • s1619Point.toJacobian := hmn
  have h : (m - n) • s1619Point.toJacobian = 0 := by
    rw [sub_zsmul, hmn']
    simp
  exact s1626ZSMulPoint_ne_zero (m - n) (sub_ne_zero.mpr hne) h

/-- **The addition identity over the universal field.** `addXYZ` at the triples at `m` and `n` is the triple at `n + m`, scaled by `ψ (n - m)`. -/
theorem s1626AddXYZ_smulField (m n : ℤ) :
    Jacobian.addXYZ pointedCurve (smulField m) (smulField n) =
      polyToField (curve.ψ (n - m)) • smulField (n + m) := by
  obtain rfl | h := eq_or_ne m n
  · rw [sub_self, WeierstrassCurve.ψ_zero, map_zero,
      Jacobian.addXYZ_self (s1626Nonsingular_smulField m).1, Jacobian.smul_fin3]
    simp
  obtain rfl | ne_neg := eq_or_ne n (-m)
  · rw [← one_smul Field (smulField m), s1625SmulField_neg, neg_add_cancel,
      Jacobian.addXYZ_smul, one_mul, neg_one_sq,
      Jacobian.addXYZ_neg (s1626Nonsingular_smulField m).1, one_smul,
      show (-m - m : ℤ) = -(2 * m) by ring, WeierstrassCurve.ψ_neg]
    rw [map_neg (f := polyToField), ← dblZ_smulField m, s1626SmulField_zero]
  refine (Jacobian.equiv_iff_eq_of_Z_eq ?hZ ?hZ0).mp (Quotient.exact ?hclass)
  · rw [Jacobian.addXYZ_Z,
      (Jacobian.smul_fin3_ext (smulField (n + m)) (polyToField (curve.ψ (n - m)))).2.2,
      s1626SmulField_Z, addZ_smulField m n, map_mul]
    rw [mul_comm]
  · rw [(Jacobian.smul_fin3_ext (smulField (n + m)) (polyToField (curve.ψ (n - m)))).2.2,
      s1626SmulField_Z]
    exact mul_ne_zero (polyToField_ψ_ne_zero (n - m) (sub_ne_zero_of_ne h.symm))
      (polyToField_ψ_ne_zero (n + m) (by omega))
  · have hne : ¬ smulField m ≈ smulField n := by
      intro hequiv
      have hpoint : m • s1619Point.toJacobian = n • s1619Point.toJacobian := by
        apply Jacobian.Point.ext_iff.mpr
        rw [s1623ZSMulPointEqSmulField_all m, s1623ZSMulPointEqSmulField_all n]
        exact Quotient.sound hequiv
      exact h (s1626ZSMulPoint_injective hpoint)
    have hadd : (m • s1619Point.toJacobian + n • s1619Point.toJacobian).point =
        ⟦Jacobian.addXYZ pointedCurve (smulField m) (smulField n)⟧ := by
      rw [Jacobian.Point.add_point, s1623ZSMulPointEqSmulField_all m,
        s1623ZSMulPointEqSmulField_all n, Jacobian.addMap_eq,
        Jacobian.add_of_not_equiv hne]
    rw [Jacobian.smul_eq _ (polyToField_ψ_ne_zero (n - m)
        (sub_ne_zero_of_ne h.symm)).isUnit,
      ← s1623ZSMulPointEqSmulField_all (n + m),
      show n + m = m + n by ring, add_zsmul, ← hadd]


theorem s1626Comp_smul {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (u : R) (P : Fin 3 → R) : f ∘ (u • P) = f u • (f ∘ P) := by
  funext i
  fin_cases i <;> simp [Jacobian.smul_fin3, map_mul]


/-- The addition identity over the universal ring. -/
theorem s1626AddXYZ_smulRing (m n : ℤ) :
    Jacobian.addXYZ s1626CurveRing (smulRing m) (smulRing n) =
      AdjoinRoot.mk Universal.curve.toAffine.polynomial (Universal.curve.ψ (n - m)) •
        smulRing (n + m) := by
  apply (IsFractionRing.injective Universal.Ring Universal.Field).comp_left
  change (algebraMap Universal.Ring Universal.Field) ∘
      Jacobian.addXYZ s1626CurveRing (smulRing m) (smulRing n) =
    (algebraMap Universal.Ring Universal.Field) ∘
      (AdjoinRoot.mk Universal.curve.toAffine.polynomial (Universal.curve.ψ (n - m)) •
        smulRing (n + m))
  rw [← Jacobian.map_addXYZ (algebraMap Universal.Ring Universal.Field)
      (smulRing m) (smulRing n)]
  rw [show Jacobian.map s1626CurveRing (algebraMap Universal.Ring Universal.Field) =
      pointedCurve from s1626CurveRing_map]
  rw [s1626Comp_smul (algebraMap Universal.Ring Universal.Field)
    (AdjoinRoot.mk Universal.curve.toAffine.polynomial (Universal.curve.ψ (n - m)))
    (smulRing (n + m))]
  rw [show (algebraMap Universal.Ring Universal.Field)
      (AdjoinRoot.mk Universal.curve.toAffine.polynomial (Universal.curve.ψ (n - m))) =
        polyToField (Universal.curve.ψ (n - m)) from rfl]
  simp only [s1626AlgebraMap_comp_smulRing]
  exact s1626AddXYZ_smulField m n


/-- The division-polynomial triple evaluated at an affine point. -/
abbrev s1626SmulEval {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) (n : ℤ) :
    Fin 3 → R := evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n]

@[simp]
theorem s1626SmulEval_zero {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    s1626SmulEval W x y 0 = ![1, 1, 0] := by
  simp [s1626SmulEval, comp_fin3, WeierstrassCurve.φ_zero,
    WeierstrassCurve.ω_zero, WeierstrassCurve.ψ_zero]

@[simp]
theorem s1626SmulEval_one {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    s1626SmulEval W x y 1 = ![x, y, 1] := by
  simp [s1626SmulEval, comp_fin3, WeierstrassCurve.φ_one,
    WeierstrassCurve.ω_one, WeierstrassCurve.ψ_one, Polynomial.evalEval_C]

theorem s1626RingEval_ψ {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (eqn : W.toAffine.Equation x y) (n : ℤ) :
    s1626RingEval W eqn
        (AdjoinRoot.mk Universal.curve.toAffine.polynomial (Universal.curve.ψ n)) =
      evalEval x y (W.ψ n) := by
  rw [s1626RingEval_mk, ← s1626EvalEval_ψ]

theorem s1626RingEval_comp_smulRing {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (eqn : W.toAffine.Equation x y) (n : ℤ) :
    s1626RingEval W eqn ∘ smulRing n = s1626SmulEval W x y n := by
  funext i
  fin_cases i <;>
    simp [smulRing, s1626SmulEval, Universal.smulPoly, s1626RingEval_mk,
      s1626EvalEval_φ, s1626EvalEval_ω, s1626EvalEval_ψ]

/-- The evaluated doubling identity. -/
theorem s1626DblXYZ_smulEval {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (eqn : W.toAffine.Equation x y) (n : ℤ) :
    Jacobian.dblXYZ W (s1626SmulEval W x y n) = s1626SmulEval W x y (2 * n) := by
  simp_rw [← s1626RingEval_comp_smulRing W eqn n,
    ← s1626RingEval_comp_smulRing W eqn (2 * n)]
  rw [← s1626DblXYZ_smulRing n]
  rw [← Jacobian.map_dblXYZ (s1626RingEval W eqn) (smulRing n)]
  rw [show Jacobian.map s1626CurveRing (s1626RingEval W eqn) = W
    from s1626Map_ringEval W eqn]

/-- The evaluated addition identity. -/
theorem s1626AddXYZ_smulEval {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (eqn : W.toAffine.Equation x y) (m n : ℤ) :
    Jacobian.addXYZ W (s1626SmulEval W x y m) (s1626SmulEval W x y n) =
      evalEval x y (W.ψ (n - m)) • s1626SmulEval W x y (n + m) := by
  simp_rw [← s1626RingEval_comp_smulRing W eqn m,
    ← s1626RingEval_comp_smulRing W eqn n,
    ← s1626RingEval_comp_smulRing W eqn (n + m)]
  rw [← s1626RingEval_ψ W eqn (n - m)]
  rw [← s1626Comp_smul (s1626RingEval W eqn)
    (AdjoinRoot.mk Universal.curve.toAffine.polynomial (Universal.curve.ψ (n - m)))
    (smulRing (n + m))]
  rw [← s1626AddXYZ_smulRing m n]
  conv_lhs =>
    arg 1
    rw [← s1626Map_ringEval W eqn]
  rw [← Jacobian.map_addXYZ (s1626RingEval W eqn) (smulRing m) (smulRing n)]

theorem s1626SmulRing_neg (n : ℤ) :
    smulRing (-n) = (-1 : Universal.Ring) • Jacobian.neg s1626CurveRing (smulRing n) := by
  apply (IsFractionRing.injective Universal.Ring Universal.Field).comp_left
  change (algebraMap Universal.Ring Universal.Field) ∘ smulRing (-n) =
    (algebraMap Universal.Ring Universal.Field) ∘
      ((-1 : Universal.Ring) • Jacobian.neg s1626CurveRing (smulRing n))
  rw [s1626AlgebraMap_comp_smulRing (-n),
    s1626Comp_smul (algebraMap Universal.Ring Universal.Field) (-1 : Universal.Ring)
      (Jacobian.neg s1626CurveRing (smulRing n))]
  rw [map_neg, map_one]
  rw [← show Jacobian.neg pointedCurve
      ((algebraMap Universal.Ring Universal.Field) ∘ smulRing n) =
      (algebraMap Universal.Ring Universal.Field) ∘
        Jacobian.neg s1626CurveRing (smulRing n) from ?_]
  · rw [s1626AlgebraMap_comp_smulRing n]
    exact s1625SmulField_neg n
  · rw [show pointedCurve =
        s1626CurveRing.map (algebraMap Universal.Ring Universal.Field)
        from s1626CurveRing_map.symm]
    exact Jacobian.map_neg (algebraMap Universal.Ring Universal.Field) (smulRing n)


theorem s1626SmulEval_neg {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (eqn : W.toAffine.Equation x y) (n : ℤ) :
    s1626SmulEval W x y (-n) = (-1 : R) • Jacobian.neg W (s1626SmulEval W x y n) := by
  rw [← s1626RingEval_comp_smulRing W eqn (-n)]
  rw [s1626SmulRing_neg n]
  rw [s1626Comp_smul (s1626RingEval W eqn) (-1 : Universal.Ring)
      (Jacobian.neg s1626CurveRing (smulRing n))]
  rw [map_neg, map_one]
  rw [← show Jacobian.neg W (s1626RingEval W eqn ∘ smulRing n) =
      (s1626RingEval W eqn) ∘ Jacobian.neg s1626CurveRing (smulRing n) from ?_]
  · rw [s1626RingEval_comp_smulRing W eqn n]
  · have h := Jacobian.map_neg (W' := s1626CurveRing) (s1626RingEval W eqn) (smulRing n)
    rw [s1626JacobianMap_ringEval W eqn] at h
    exact h


/-- **The integer multiples of a nonsingular affine point are the evaluated division-polynomial triple.** -/
theorem s1626ZSMulPointEqSmulEval {F : Type*} [Field F] (W : WeierstrassCurve F)
    {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    (n • Jacobian.Point.fromAffine (Affine.Point.some x y h)).point =
      ⟦s1626SmulEval W x y n⟧ := by
  induction n using Int.negInduction with
  | nat n =>
    refine Nat.strong_induction_on n ?_
    intro n ih
    obtain _ | _ | n := n
    · rw [Nat.cast_zero, zero_smul, s1626SmulEval_zero]
      rfl
    · rw [Nat.cast_one, one_smul, s1626SmulEval_one]
      rfl
    obtain ⟨n, rfl | rfl⟩ := n.even_or_odd'
    · rw [show (2 * n + 1 + 1 : ℕ) = 2 * (n + 1) by omega, Nat.cast_mul,
        mul_smul, Nat.cast_ofNat, two_zsmul, Jacobian.Point.add_point,
        ih (n + 1) (by omega), Jacobian.addMap_eq,
        Jacobian.add_self, s1626DblXYZ_smulEval W h.1]
    · rw [show 2 * n + 1 + 1 + 1 = (n + 1) + (n + 1 + 1) by omega,
        Nat.cast_add, add_smul]
      have hne : (↑(n + 1) : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some x y h) ≠
          (↑(n + 1 + 1) : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some x y h) := by
        rw [ne_comm, ← sub_ne_zero, ← sub_smul]
        push_cast
        simp only [add_sub_cancel_left, one_smul]
        exact Jacobian.Point.fromAffine_some_ne_zero h
      have hnequiv : ¬ (s1626SmulEval W x y ↑(n + 1) ≈ s1626SmulEval W x y ↑(n + 1 + 1)) := by
        intro hequiv
        refine hne (Jacobian.Point.ext_iff.mpr ?_)
        rw [ih (n + 1) (by omega), ih (n + 1 + 1) (by omega)]
        exact Quotient.sound hequiv
      have hcast : ((n + 1 + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
      rw [Jacobian.Point.add_point, ih (n + 1) (by omega), ih (n + 1 + 1) (by omega),
        Jacobian.addMap_eq, Jacobian.add_of_not_equiv hnequiv, hcast,
        s1626AddXYZ_smulEval W h.1, add_sub_cancel_left,
        WeierstrassCurve.ψ_one, Polynomial.evalEval_one, one_smul]
      congrm(⟦s1626SmulEval W x y ?_⟧)
      ring
  | neg ih n =>
    simp_rw [_root_.neg_smul, Jacobian.Point.neg_point, ih n, eq_comm]
    refine Quotient.sound ⟨-1, ?_⟩
    simp_rw [s1626SmulEval_neg W h.1 n]
    rfl

end LeanFormal.IUT.XiFPaper.S1626AddXYZSmulEvalPortActual
end