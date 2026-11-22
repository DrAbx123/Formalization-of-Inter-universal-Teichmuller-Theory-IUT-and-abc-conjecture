import tmp.sheaf.xif.paper.S2482QiNontrivialActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.EraseLead

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.S2482OrderTwoAlgAutClassificationActualV2

open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2482QiNontrivialActual
open Polynomial
open scoped Polynomial.Bivariate

abbrev Poly : Type := Polynomial F

abbrev Wc : WeierstrassCurve F := S2482Curve

abbrev A : Type := WeierstrassCurve.Affine.CoordinateRing Wc

/-- The cubic x^3 - x. -/
noncomputable def curveG : Poly := Polynomial.X ^ 3 - Polynomial.X

noncomputable def xA : A := (Polynomial.X : Poly) • (1 : A)

noncomputable def yA : A :=
  WeierstrassCurve.Affine.CoordinateRing.mk Wc (Polynomial.X : Polynomial Poly)

noncomputable def eMv : MvPolynomial (Fin 2) F ≃ₐ[F] Polynomial Poly :=
  (Polynomial.Bivariate.equivMvPolynomial F).symm

lemma eMv_affinePolynomial :
    eMv S2482AffinePolynomial = WeierstrassCurve.Affine.polynomial Wc := by
  simp [eMv, Wc, S2482AffinePolynomial,
    LeanFormal.IUT.IUTII.Frobenioid.Example36.weierstrassAffinePolynomial,
    S2482Curve, WeierstrassCurve.Affine.polynomial]

noncomputable def REquiv : S2482CoordinateRing ≃ₐ[F] A :=
  Ideal.quotientEquivAlg (Ideal.span {S2482AffinePolynomial})
    (Ideal.span {WeierstrassCurve.Affine.polynomial Wc}) eMv (by
      rw [Ideal.map_span, Set.image_singleton]
      have h : (↑eMv : MvPolynomial (Fin 2) F →+* Polynomial Poly)
          S2482AffinePolynomial = WeierstrassCurve.Affine.polynomial Wc := by
        simpa using eMv_affinePolynomial
      rw [h])

noncomputable def xR : S2482CoordinateRing :=
  Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 0)

noncomputable def yR : S2482CoordinateRing :=
  Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 1)

lemma REquiv_xR : REquiv xR = xA := by
  unfold REquiv xR
  erw [Ideal.quotientEquivAlg_mk]
  have h : eMv (MvPolynomial.X 0) =
      (Polynomial.C (Polynomial.X : Poly) : Polynomial Poly) := by
    simp [eMv, Polynomial.Bivariate.equivMvPolynomial_symm_X_0]
  rw [h, xA, WeierstrassCurve.Affine.CoordinateRing.smul, mul_one]
  rfl

lemma REquiv_yR : REquiv yR = yA := by
  unfold REquiv yR
  erw [Ideal.quotientEquivAlg_mk]
  simp [eMv, yA, Polynomial.Bivariate.equivMvPolynomial_symm_X_1]
  rfl

lemma sigma_xR : S2482CoordinateRingInvolution xR = xR := by
  simp [xR, S2482CoordinateRingInvolution, S2482AffineInvolutionAlgHom,
    Ideal.Quotient.liftₐ]

lemma sigma_yR : S2482CoordinateRingInvolution yR = -yR := by
  simp [yR, S2482CoordinateRingInvolution, S2482AffineInvolutionAlgHom,
    Ideal.Quotient.liftₐ]

noncomputable def signA : A →ₐ[F] A :=
  REquiv.toAlgHom.comp (S2482CoordinateRingInvolution.comp REquiv.symm.toAlgHom)

lemma REquiv_symm_xA : REquiv.symm xA = xR := by
  rw [← REquiv_xR, AlgEquiv.symm_apply_apply]

lemma REquiv_symm_yA : REquiv.symm yA = yR := by
  rw [← REquiv_yR, AlgEquiv.symm_apply_apply]

lemma signA_xA : signA xA = xA := by
  change REquiv (S2482CoordinateRingInvolution (REquiv.symm xA)) = xA
  rw [REquiv_symm_xA, sigma_xR, REquiv_xR]

lemma signA_yA : signA yA = -yA := by
  change REquiv (S2482CoordinateRingInvolution (REquiv.symm yA)) = -yA
  rw [REquiv_symm_yA, sigma_yR, map_neg, REquiv_yR]

lemma of_eq_aeval (p : Poly) :
    AdjoinRoot.of (WeierstrassCurve.Affine.polynomial Wc) p = Polynomial.aeval xA p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [map_add, hp, hq]
  | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      have hC : AdjoinRoot.of (WeierstrassCurve.Affine.polynomial Wc)
          (Polynomial.C c) = algebraMap F A c := by
        rw [show AdjoinRoot.of (WeierstrassCurve.Affine.polynomial Wc)
            (Polynomial.C c) = AdjoinRoot.mk (WeierstrassCurve.Affine.polynomial Wc)
              (Polynomial.C (Polynomial.C c)) from rfl]
        rw [AdjoinRoot.mk_C, IsScalarTower.algebraMap_apply F Poly A]
        rfl
      have hX : AdjoinRoot.of (WeierstrassCurve.Affine.polynomial Wc)
          (Polynomial.X : Poly) = xA := by
        rw [show AdjoinRoot.of (WeierstrassCurve.Affine.polynomial Wc)
            (Polynomial.X : Poly) = AdjoinRoot.mk (WeierstrassCurve.Affine.polynomial Wc)
              (Polynomial.C (Polynomial.X : Poly)) from rfl]
        rw [xA, WeierstrassCurve.Affine.CoordinateRing.smul, mul_one]
      have hL : AdjoinRoot.of (WeierstrassCurve.Affine.polynomial Wc)
          (Polynomial.C c * Polynomial.X ^ n) =
          AdjoinRoot.of (WeierstrassCurve.Affine.polynomial Wc) (Polynomial.C c) *
            (AdjoinRoot.of (WeierstrassCurve.Affine.polynomial Wc)
              (Polynomial.X : Poly)) ^ n := by
        rw [map_mul, map_pow]
      have hR : Polynomial.aeval xA (Polynomial.C c * Polynomial.X ^ n) =
          algebraMap F A c * xA ^ n := by
        simp
      rw [hL, hR, hC, hX]

lemma algHom_ext_A {f g : A →ₐ[F] A}
    (hx : f xA = g xA) (hy : f yA = g yA) : f = g := by
  apply AlgHom.coe_ringHom_injective
  apply AdjoinRoot.ringHom_ext (p := WeierstrassCurve.Affine.polynomial Wc)
  · apply RingHom.ext
    intro p
    change f (AdjoinRoot.of (WeierstrassCurve.Affine.polynomial Wc) p) =
      g (AdjoinRoot.of (WeierstrassCurve.Affine.polynomial Wc) p)
    rw [of_eq_aeval]
    rw [← Polynomial.aeval_algHom_apply f xA p, ← Polynomial.aeval_algHom_apply g xA p, hx]
  · exact hy

lemma algHom_ext_R {f g : S2482CoordinateRing →ₐ[F] S2482CoordinateRing}
    (hx : f xR = g xR) (hy : f yR = g yR) : f = g := by
  apply Ideal.Quotient.algHom_ext F
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simpa [xR] using hx
  · simpa [yR] using hy

lemma yA_sq : yA ^ 2 = curveG • (1 : A) := by
  have hp : WeierstrassCurve.Affine.polynomial Wc =
      (Polynomial.X : Polynomial Poly) ^ 2 - Polynomial.C curveG := by
    simp [WeierstrassCurve.Affine.polynomial, Wc, S2482Curve, curveG]
    ring
  rw [yA, ← map_pow]
  rw [show curveG • (1 : A) = AdjoinRoot.mk (WeierstrassCurve.Affine.polynomial Wc)
      (Polynomial.C curveG) from by
    rw [WeierstrassCurve.Affine.CoordinateRing.smul, mul_one]]
  rw [AdjoinRoot.mk_eq_mk]
  rw [hp]

noncomputable def coords (z : A) : Poly × Poly :=
  let h := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq (W' := Wc) z
  (Classical.choose h, Classical.choose (Classical.choose_spec h))

lemma coords_spec (z : A) :
    (coords z).1 • (1 : A) + (coords z).2 • yA = z := by
  simpa [coords, yA] using
    Classical.choose_spec
      (Classical.choose_spec
        (WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq (W' := Wc) z))

lemma coords_eq_of_eq {p q : Poly} {z : A}
    (h : p • (1 : A) + q • yA = z) : coords z = (p, q) := by
  have hz := coords_spec z
  have hzero : (p - (coords z).1) • (1 : A) + (q - (coords z).2) • yA = 0 := by
    have hdiff : (p • (1 : A) + q • yA) -
        ((coords z).1 • (1 : A) + (coords z).2 • yA) = 0 := by
      rw [h, hz, sub_self]
    simpa [sub_smul, add_sub_add_comm] using hdiff
  obtain ⟨h1, h2⟩ :=
    WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero (W' := Wc) hzero
  exact Prod.ext (sub_eq_zero.mp h1).symm (sub_eq_zero.mp h2).symm

lemma coords_zero : coords (0 : A) = (0, 0) := by
  apply coords_eq_of_eq
  simp

lemma coords_add (z w : A) :
    coords (z + w) = ((coords z).1 + (coords w).1,
      (coords z).2 + (coords w).2) := by
  apply coords_eq_of_eq
  calc
    ((coords z).1 + (coords w).1) • (1 : A) +
        ((coords z).2 + (coords w).2) • yA
        = ((coords z).1 • (1 : A) + (coords z).2 • yA) +
          ((coords w).1 • (1 : A) + (coords w).2 • yA) := by
            rw [add_smul, add_smul]; abel
    _ = z + w := by rw [coords_spec z, coords_spec w]

lemma coords_xA : coords xA = ((Polynomial.X : Poly), 0) := by
  apply coords_eq_of_eq
  simp [xA]

lemma coords_yA : coords yA = (0, 1) := by
  apply coords_eq_of_eq
  simp [yA]

noncomputable def W (z : A) : WithBot ℕ := (Algebra.norm Poly z).degree

lemma W_eq (z : A) :
    W z = max (2 • (coords z).1.degree) (2 • (coords z).2.degree + 3) := by
  rw [W]
  conv_lhs => rw [← coords_spec z]
  simpa [yA] using
    (WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis
      (W' := Wc) (coords z).1 (coords z).2)

lemma W_mul (z w : A) : W (z * w) = W z + W w := by
  rw [W, W, W, map_mul (Algebra.norm Poly), Polynomial.degree_mul]

lemma W_const (c : F) (hc : c ≠ 0) : W (algebraMap F A c) = 0 := by
  have hcoords : coords (algebraMap F A c) =
      (Polynomial.C c, 0) := by
    apply coords_eq_of_eq
    rw [zero_smul, add_zero]
    rw [Algebra.smul_def, mul_one]
    rw [IsScalarTower.algebraMap_apply F Poly A]
    rfl
  rw [W_eq, hcoords]
  simp [hc]

lemma W_pow (u : A) (d : ℕ) (hd : W u = (d : WithBot ℕ)) (n : ℕ) :
    W (u ^ n) = (n * d : ℕ) := by
  induction n with
  | zero =>
      simpa using W_const (1 : F) one_ne_zero
  | succ n ih =>
      rw [pow_succ, W_mul, ih, hd]
      push_cast
      ring

lemma two_nsmul_degree_eq_of_ne_zero {p : Poly} (hp : p ≠ 0) :
    2 • p.degree = ((2 * p.natDegree : ℕ) : WithBot ℕ) := by
  rw [Polynomial.degree_eq_natDegree hp, two_nsmul]
  norm_cast
  ring

lemma two_nsmul_degree_add_three_eq_of_ne_zero {p : Poly} (hp : p ≠ 0) :
    2 • p.degree + 3 = ((2 * p.natDegree + 3 : ℕ) : WithBot ℕ) := by
  rw [two_nsmul_degree_eq_of_ne_zero hp]
  norm_cast

lemma degree_mul_lt_of_bounds {p1 p2 : Poly} {n : ℕ}
    (h1 : 2 • p1.degree < (n : WithBot ℕ))
    (h2 : 2 • p2.degree ≤ (n : WithBot ℕ)) :
    (p1 * p2).degree < (n : WithBot ℕ) := by
  by_cases hp1 : p1 = 0
  · simp [hp1]
  by_cases hp2 : p2 = 0
  · simp [hp2]
  have h1' : 2 * p1.natDegree < n := by
    have := h1
    rw [two_nsmul_degree_eq_of_ne_zero hp1] at this
    exact_mod_cast this
  have h2' : 2 * p2.natDegree ≤ n := by
    have := h2
    rw [two_nsmul_degree_eq_of_ne_zero hp2] at this
    exact_mod_cast this
  have hsum : p1.natDegree + p2.natDegree < n := by omega
  have hdeg : (p1 * p2).degree =
      ((p1.natDegree + p2.natDegree : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_mul, Polynomial.degree_eq_natDegree hp1,
      Polynomial.degree_eq_natDegree hp2]
    push_cast
    rfl
  rw [hdeg]
  exact_mod_cast hsum

lemma curveG_natDegree : curveG.natDegree = 3 := by
  rw [curveG]
  have h : (Polynomial.X : Poly).natDegree < ((Polynomial.X : Poly) ^ 3).natDegree := by
    rw [Polynomial.natDegree_X_pow]; norm_num
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt h, Polynomial.natDegree_X_pow]

lemma curveG_degree : curveG.degree = (3 : WithBot ℕ) := by
  rw [curveG]
  rw [Polynomial.degree_sub_eq_left_of_degree_lt]
  · simp
  · simp

lemma degree_mul_curveG_lt_of_bounds {q1 q2 : Poly} {n : ℕ}
    (h1 : 2 • q1.degree + 3 < (n : WithBot ℕ))
    (h2 : 2 • q2.degree + 3 ≤ (n : WithBot ℕ)) :
    (q1 * q2 * curveG).degree < (n : WithBot ℕ) := by
  by_cases hq1 : q1 = 0
  · simp [hq1]
  by_cases hq2 : q2 = 0
  · simp [hq2]
  have h1' : 2 * q1.natDegree + 3 < n := by
    have := h1
    rw [two_nsmul_degree_add_three_eq_of_ne_zero hq1] at this
    exact_mod_cast this
  have h2' : 2 * q2.natDegree + 3 ≤ n := by
    have := h2
    rw [two_nsmul_degree_add_three_eq_of_ne_zero hq2] at this
    exact_mod_cast this
  have hsum : q1.natDegree + q2.natDegree + 3 < n := by omega
  have hdeg : (q1 * q2 * curveG).degree =
      ((q1.natDegree + q2.natDegree + 3 : ℕ) : WithBot ℕ) := by
    rw [mul_assoc, Polynomial.degree_mul, Polynomial.degree_mul,
      Polynomial.degree_eq_natDegree hq1, Polynomial.degree_eq_natDegree hq2,
      curveG_degree]
    push_cast
    rfl
  rw [hdeg]
  exact_mod_cast hsum

def wt (p q : Poly) : WithBot ℕ := max (2 • p.degree) (2 • q.degree + 3)

lemma wt_mul_lt {p1 q1 p2 q2 : Poly} (h : wt p1 q1 < wt p2 q2) :
    (p1 * p2 - q1 * q2 * curveG).degree < wt p2 q2 := by
  have hne : wt p2 q2 ≠ ⊥ := by
    intro hbot
    rw [hbot] at h
    exact (not_lt_of_ge bot_le) h
  obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hne
  have hn' : wt p2 q2 = (n : WithBot ℕ) := hn.symm
  have h1p : 2 • p1.degree < (n : WithBot ℕ) := by
    have hle : 2 • p1.degree ≤ wt p1 q1 := le_max_left _ _
    have := lt_of_le_of_lt hle h
    rwa [hn'] at this
  have h1q : 2 • q1.degree + 3 < (n : WithBot ℕ) := by
    have hle : 2 • q1.degree + 3 ≤ wt p1 q1 := le_max_right _ _
    have := lt_of_le_of_lt hle h
    rwa [hn'] at this
  have h2p : 2 • p2.degree ≤ (n : WithBot ℕ) := by
    have hle : 2 • p2.degree ≤ wt p2 q2 := le_max_left _ _
    rwa [hn'] at hle
  have h2q : 2 • q2.degree + 3 ≤ (n : WithBot ℕ) := by
    have hle : 2 • q2.degree + 3 ≤ wt p2 q2 := le_max_right _ _
    rwa [hn'] at hle
  have hp := degree_mul_lt_of_bounds h1p h2p
  have hq := degree_mul_curveG_lt_of_bounds h1q h2q
  have hlt := lt_of_le_of_lt (Polynomial.degree_sub_le (p1 * p2) (q1 * q2 * curveG))
    (max_lt hp hq)
  rwa [← hn'] at hlt

end LeanFormal.IUT.XiFPaper.S2482OrderTwoAlgAutClassificationActualV2
end
