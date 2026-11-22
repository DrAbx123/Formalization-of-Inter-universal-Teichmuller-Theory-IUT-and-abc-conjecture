import tmp.sheaf.xif.paper.S2482QiNontrivialActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2482OrderTwoAlgAutClassificationActualV3

open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2482QiNontrivialActual
open Polynomial
open scoped Polynomial.Bivariate

/-- The Weierstrass curve y^2 = x^3 - x over F. -/
abbrev W : WeierstrassCurve F := S2482Curve

/-- The defining polynomial of W. -/
noncomputable abbrev Wpoly : Polynomial (Polynomial F) :=
  WeierstrassCurve.Affine.polynomial W

/-- Mathlib's affine coordinate ring of W, i.e. F[X,Y]/(Y^2 - X^3 + X). -/
abbrev A : Type := WeierstrassCurve.Affine.CoordinateRing W

/-- The class of X in the affine coordinate ring. -/
noncomputable def xC : A :=
  WeierstrassCurve.Affine.CoordinateRing.mk W (C (X : Polynomial F))

/-- The class of Y in the affine coordinate ring. -/
noncomputable def yC : A :=
  WeierstrassCurve.Affine.CoordinateRing.mk W (Y : Polynomial (Polynomial F))

theorem Wpoly_eq : Wpoly =
    (X : Polynomial (Polynomial F)) ^ 2 - C ((X : Polynomial F) ^ 3 - X) := by
  simp [Wpoly, W, S2482Curve, WeierstrassCurve.Affine.polynomial]
  ring

theorem yC_sq : yC ^ 2 = xC ^ 3 - xC := by
  have h : AdjoinRoot.mk Wpoly
      ((X : Polynomial (Polynomial F)) ^ 2 - C ((X : Polynomial F) ^ 3 - X)) = 0 := by
    rw [← Wpoly_eq]
    exact AdjoinRoot.mk_self
  have h' : yC ^ 2 - (xC ^ 3 - xC) = 0 := by
    simpa [yC, xC, map_sub, map_pow] using h
  linear_combination h'

/-- The bivariate equivalence used to compare the two coordinate rings. -/
noncomputable def eMv : MvPolynomial (Fin 2) F ≃ₐ[F] Polynomial (Polynomial F) :=
  (Polynomial.Bivariate.equivMvPolynomial F).symm

theorem eMv_affinePolynomial : eMv S2482AffinePolynomial = Wpoly := by
  simp [eMv, Wpoly, W, S2482AffinePolynomial,
    LeanFormal.IUT.IUTII.Frobenioid.Example36.weierstrassAffinePolynomial,
    S2482Curve, WeierstrassCurve.Affine.polynomial]

/-- The F-algebra identification between the S2482 coordinate ring and Mathlib's
affine coordinate ring of y^2 = x^3 - x. -/
noncomputable def e : S2482CoordinateRing ≃ₐ[F] A :=
  Ideal.quotientEquivAlg (I := Ideal.span {S2482AffinePolynomial})
    (J := Ideal.span {Wpoly}) eMv (by
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span {Wpoly} = Ideal.span {eMv S2482AffinePolynomial}
      rw [eMv_affinePolynomial])

theorem e_x : e (Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial})
    (MvPolynomial.X 0)) = xC := by
  rw [e]
  change Ideal.Quotient.mk (Ideal.span {Wpoly}) (eMv (MvPolynomial.X 0)) =
    Ideal.Quotient.mk (Ideal.span {Wpoly}) (C (X : Polynomial F))
  rw [eMv, Polynomial.Bivariate.equivMvPolynomial_symm_X_0]

theorem e_y : e (Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial})
    (MvPolynomial.X 1)) = yC := by
  rw [e]
  change Ideal.Quotient.mk (Ideal.span {Wpoly}) (eMv (MvPolynomial.X 1)) =
    Ideal.Quotient.mk (Ideal.span {Wpoly}) (X : Polynomial (Polynomial F))
  rw [eMv, Polynomial.Bivariate.equivMvPolynomial_symm_X_1]


/-! ## The degree of an element of the coordinate ring -/

open WeierstrassCurve.Affine

instance instIsDomainA : IsDomain A := inferInstance

instance instFreeA : Module.Free (Polynomial F) A :=
  (WeierstrassCurve.Affine.monic_polynomial (W := W)).free_adjoinRoot

instance instFiniteA : Module.Finite (Polynomial F) A :=
  (WeierstrassCurve.Affine.monic_polynomial (W := W)).finite_adjoinRoot

/-- The degree of an element of the coordinate ring, defined as the degree of its
norm to `F[X]`. By `degree_norm_smul_basis` this is the weighted degree of its
normal form `p + qY`, namely `max (2 deg p) (2 deg q + 3)`. -/
noncomputable def d (z : A) : WithBot ℕ :=
  (Algebra.norm (Polynomial F) z).degree

@[simp]
theorem d_zero : d (0 : A) = ⊥ := by
  simp [d]

theorem d_eq_bot_iff {z : A} : d z = ⊥ ↔ z = 0 := by
  rw [d, Polynomial.degree_eq_bot, Algebra.norm_eq_zero_iff]

theorem d_ne_bot_iff {z : A} : d z ≠ ⊥ ↔ z ≠ 0 :=
  not_congr d_eq_bot_iff

@[simp]
theorem d_one : d (1 : A) = 0 := by
  simp [d]

theorem d_smul_basis (p q : Polynomial F) :
    d (p • (1 : A) + q • yC) = max (2 • p.degree) (2 • q.degree + 3) := by
  rw [d]
  simpa [yC] using
    (WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis (W' := W) p q)

theorem d_algebraMap {c : F} (hc : c ≠ 0) : d (algebraMap F A c) = 0 := by
  have h : algebraMap F A c = (C c) • (1 : A) := by
    rw [IsScalarTower.algebraMap_apply F (Polynomial F) A,
      ← Polynomial.C_eq_algebraMap, Algebra.algebraMap_eq_smul_one]
  rw [h]
  have h2 := d_smul_basis (C c) (0 : Polynomial F)
  rw [zero_smul, add_zero] at h2
  rw [h2, Polynomial.degree_C hc]
  simp

theorem d_mul (x y : A) : d (x * y) = d x + d y := by
  by_cases hx : x = 0
  · simp [d, hx]
  by_cases hy : y = 0
  · simp [d, hy]
  rw [d, d, d, map_mul, Polynomial.degree_mul]

theorem d_pow (z : A) (n : ℕ) : d (z ^ n) = n • d z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, d_mul, ih, succ_nsmul]

theorem d_neg (z : A) : d (-z) = d z := by
  rw [← neg_one_mul, d_mul]
  have h : d (-1 : A) = 0 := by
    simpa using d_algebraMap (c := (-1 : F)) (by norm_num)
  rw [h, zero_add]

@[simp]
theorem d_xC : d xC = 2 := by
  have h : xC = (X : Polynomial F) • (1 : A) := by
    rw [WeierstrassCurve.Affine.CoordinateRing.smul, mul_one]
    rfl
  rw [h]
  simpa using d_smul_basis (X : Polynomial F) (0 : Polynomial F)

@[simp]
theorem d_yC : d yC = 3 := by
  have h : yC = (0 : Polynomial F) • (1 : A) + (1 : Polynomial F) • yC := by
    rw [zero_smul, zero_add, one_smul]
  rw [h]
  simpa using d_smul_basis (0 : Polynomial F) (1 : Polynomial F)

/-- `2 • x` distributes over `max` on `WithBot ℕ`. -/
lemma two_nsmul_max (a b : WithBot ℕ) : 2 • max a b = max (2 • a) (2 • b) := by
  rw [two_nsmul, two_nsmul, two_nsmul]
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (add_le_add h h)]
  · rw [max_eq_left h, max_eq_left (add_le_add h h)]

lemma two_nsmul_degree_add_le (p q : Polynomial F) :
    2 • (p + q).degree ≤ max (2 • p.degree) (2 • q.degree) := by
  have h1 : (p + q).degree ≤ max p.degree q.degree := Polynomial.degree_add_le p q
  calc 2 • (p + q).degree = (p + q).degree + (p + q).degree := two_nsmul _
    _ ≤ max p.degree q.degree + max p.degree q.degree := add_le_add h1 h1
    _ = 2 • (max p.degree q.degree) := (two_nsmul _).symm
    _ = max (2 • p.degree) (2 • q.degree) := two_nsmul_max _ _

lemma max_add_three (a b : WithBot ℕ) : max a b + 3 = max (a + 3) (b + 3) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, add_comm b 3, add_comm a 3]
    exact (max_eq_right (add_le_add_right h 3)).symm
  · rw [max_eq_left h, add_comm a 3, add_comm b 3]
    exact (max_eq_left (add_le_add_right h 3)).symm

lemma zero_le_of_ne_bot {a : WithBot ℕ} (ha : a ≠ ⊥) : (0 : WithBot ℕ) ≤ a := by
  cases a with
  | bot => exact absurd rfl ha
  | coe n => exact WithBot.coe_le_coe.mpr (Nat.zero_le n)

lemma nsmul_nonneg {a : WithBot ℕ} (ha : a ≠ ⊥) (k : ℕ) : (0 : WithBot ℕ) ≤ k • a := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [succ_nsmul]
      exact add_nonneg ih (zero_le_of_ne_bot ha)

lemma nsmul_le_nsmul_of_ne_bot {a : WithBot ℕ} (ha : a ≠ ⊥) {m n : ℕ} (h : m ≤ n) :
    m • a ≤ n • a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_nsmul]
  calc m • a = m • a + 0 := (add_zero _).symm
    _ ≤ m • a + k • a := by simpa using le_add_of_nonneg_right (nsmul_nonneg ha k)

/-- The degree is subadditive. -/
theorem d_add_le (x y : A) : d (x + y) ≤ max (d x) (d y) := by
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq x
  obtain ⟨p', q', rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq y
  change d ((p • (1 : A) + q • yC) + (p' • (1 : A) + q' • yC)) ≤
    max (d (p • (1 : A) + q • yC)) (d (p' • (1 : A) + q' • yC))
  have hsum : (p • (1 : A) + q • yC) + (p' • (1 : A) + q' • yC) =
      (p + p') • (1 : A) + (q + q') • yC := by
    rw [add_smul, add_smul]
    abel
  rw [hsum, d_smul_basis, d_smul_basis, d_smul_basis]
  have hA : 2 • (p + p').degree ≤ max (2 • p.degree) (2 • p'.degree) :=
    two_nsmul_degree_add_le p p'
  have hB : 2 • (q + q').degree + 3 ≤ max (2 • q.degree + 3) (2 • q'.degree + 3) := by
    calc 2 • (q + q').degree + 3 ≤ max (2 • q.degree) (2 • q'.degree) + 3 := by
          exact add_le_add_left (two_nsmul_degree_add_le q q') 3
      _ = max (2 • q.degree + 3) (2 • q'.degree + 3) := max_add_three _ _
  refine max_le ?_ ?_
  · refine hA.trans (max_le ?_ ?_)
    · exact le_trans (le_max_left _ _) (le_max_left _ _)
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · refine hB.trans (max_le ?_ ?_)
    · exact le_trans (le_max_right _ _) (le_max_left _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- The `F[X]`-scalar action on the coordinate ring is polynomial evaluation at `x`. -/
lemma smul_one_eq_aeval (p : Polynomial F) :
    p • (1 : A) = Polynomial.aeval xC p := by
  rw [← Algebra.algebraMap_eq_smul_one]
  change IsScalarTower.toAlgHom F (Polynomial F) A p = Polynomial.aeval xC p
  rw [Polynomial.eval_unique (IsScalarTower.toAlgHom F (Polynomial F) A) p]
  change Polynomial.eval₂ (algebraMap F A)
    ((IsScalarTower.toAlgHom F (Polynomial F) A) (X : Polynomial F)) p =
    Polynomial.eval₂ (algebraMap F A) xC p
  rfl

lemma nsmul_lt_nsmul_of_pos {a : WithBot ℕ} (ha : 0 < a) {m n : ℕ} (h : m < n) :
    m • a < n • a := by
  cases a with
  | bot => simp at ha
  | coe a =>
      have ha0 : 0 < a := by simpa using ha
      have h' : m • a < n • a := Nat.mul_lt_mul_of_pos_right h ha0
      exact_mod_cast h'

/-- Upper bound: the degree of `P(z)` is at most `deg P` times the degree of `z`. -/
theorem d_aeval_le_of_le (z : A) (hz : z ≠ 0) :
    ∀ (N : ℕ) (P : Polynomial F), P.natDegree ≤ N → d (Polynomial.aeval z P) ≤ N • d z := by
  intro N
  induction N with
  | zero =>
      intro P hP
      have hP0 : P.natDegree = 0 := Nat.le_zero.mp hP
      have hdeg0 : P.degree ≤ 0 := by
        rcases eq_or_ne P 0 with h | h
        · simp [h]
        · rw [Polynomial.degree_eq_natDegree h, hP0]; simp
      rw [Polynomial.eq_C_of_degree_le_zero hdeg0, Polynomial.aeval_C]
      by_cases hc : P.coeff 0 = 0
      · simp [hc]
      · rw [d_algebraMap hc]
        simp
  | succ N ih =>
      intro P hP
      by_cases hle : P.natDegree ≤ N
      · exact (ih P hle).trans (nsmul_le_nsmul_of_ne_bot (d_ne_bot_iff.mpr hz) (Nat.le_succ N))
      · have hPpos : 0 < P.natDegree := by omega
        have hPne : P ≠ 0 := by
          intro h; rw [h] at hPpos; simp at hPpos
        have hnd : P.natDegree = N + 1 := by omega
        obtain ⟨c, hc⟩ : ∃ c, P.leadingCoeff = c := ⟨_, rfl⟩
        have hc0 : c ≠ 0 := by rw [← hc]; exact Polynomial.leadingCoeff_ne_zero.mpr hPne
        have hdecomp : P = P.eraseLead + C c * X ^ (N + 1) := by
          rw [← hc, ← hnd, Polynomial.eraseLead_add_C_mul_X_pow]
        have hR : P.eraseLead.natDegree ≤ N := by
          have hle' := Polynomial.eraseLead_natDegree_le (f := P)
          omega
        have hdR : d (Polynomial.aeval z P.eraseLead) ≤ N • d z := ih _ hR
        have hdTop : d (Polynomial.aeval z (C c * X ^ (N + 1))) = (N + 1) • d z := by
          rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
          rw [d_mul, d_algebraMap hc0, d_pow, zero_add]
        rw [hdecomp, map_add]
        refine (d_add_le _ _).trans ?_
        rw [hdTop]
        exact max_le (hdR.trans (nsmul_le_nsmul_of_ne_bot (d_ne_bot_iff.mpr hz) (Nat.le_succ N)))
          (le_of_eq rfl)

/-- Lower bound: for nonconstant `P`, the degree of `P(z)` is at least `deg P` times `d z`. -/
theorem d_aeval_ge (z : A) (hz : 0 < d z) (P : Polynomial F) (hP : P ≠ 0) :
    P.natDegree • d z ≤ d (Polynomial.aeval z P) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, d_zero] at hz
    exact (not_lt_of_ge bot_le) hz
  by_cases hn : P.natDegree = 0
  · have hdeg0 : P.degree ≤ 0 := by
      rw [Polynomial.degree_eq_natDegree hP, hn]; simp
    have hc : P.coeff 0 ≠ 0 := by
      intro hc
      have hP0 : P = 0 := by
        rw [Polynomial.eq_C_of_degree_le_zero hdeg0, hc, Polynomial.C_0]
      exact hP hP0
    rw [Polynomial.eq_C_of_degree_le_zero hdeg0, Polynomial.aeval_C,
      d_algebraMap hc]
    simp
  · have hnpos : 0 < P.natDegree := Nat.pos_of_ne_zero hn
    obtain ⟨c, hc⟩ : ∃ c, P.leadingCoeff = c := ⟨_, rfl⟩
    have hc0 : c ≠ 0 := by
      rw [← hc]
      exact Polynomial.leadingCoeff_ne_zero.mpr hP
    have hdecomp : P = P.eraseLead + C c * X ^ P.natDegree := by
      rw [← hc, Polynomial.eraseLead_add_C_mul_X_pow]
    have hR : P.eraseLead.natDegree ≤ P.natDegree - 1 :=
      Polynomial.eraseLead_natDegree_le (f := P)
    have hdR : d (Polynomial.aeval z P.eraseLead) ≤ (P.natDegree - 1) • d z :=
      d_aeval_le_of_le z hz0 (P.natDegree - 1) _ hR
    have htop : d (Polynomial.aeval z (C c * X ^ P.natDegree)) = P.natDegree • d z := by
      rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
      rw [d_mul, d_algebraMap hc0, d_pow, zero_add]
    have hsub : P - P.eraseLead = C c * X ^ P.natDegree := by
      nth_rw 1 [hdecomp]
      rw [add_sub_cancel_left]
    have hdiff : Polynomial.aeval z P - Polynomial.aeval z P.eraseLead =
        Polynomial.aeval z (C c * X ^ P.natDegree) := by
      rw [← map_sub, hsub]
    have hstep1 : d (Polynomial.aeval z P - Polynomial.aeval z P.eraseLead) ≤
        max (d (Polynomial.aeval z P)) (d (Polynomial.aeval z P.eraseLead)) := by
      rw [sub_eq_add_neg]
      refine (d_add_le _ _).trans ?_
      rw [d_neg]
    have hstep2 : P.natDegree • d z =
        d (Polynomial.aeval z P - Polynomial.aeval z P.eraseLead) := by
      rw [hdiff, htop]
    have hstep3 : max (d (Polynomial.aeval z P)) (d (Polynomial.aeval z P.eraseLead)) ≤
        max (d (Polynomial.aeval z P)) ((P.natDegree - 1) • d z) :=
      max_le_max (le_refl _) hdR
    have hstep4 : max (d (Polynomial.aeval z P)) ((P.natDegree - 1) • d z) ≤
        d (Polynomial.aeval z P) := by
      have hle : (P.natDegree - 1) • d z ≤ d (Polynomial.aeval z P) := by
        by_contra hcon
        have hlt' : d (Polynomial.aeval z P) < (P.natDegree - 1) • d z := lt_of_not_ge hcon
        have hlt : (P.natDegree - 1) • d z < P.natDegree • d z :=
          nsmul_lt_nsmul_of_pos hz (by omega)
        have hmaxlt : max (d (Polynomial.aeval z P)) ((P.natDegree - 1) • d z) <
            P.natDegree • d z := max_lt (hlt'.trans hlt) hlt
        have hmain : P.natDegree • d z ≤ max (d (Polynomial.aeval z P))
            ((P.natDegree - 1) • d z) := hstep2 ▸ hstep1.trans hstep3
        exact lt_irrefl _ (hmain.trans_lt hmaxlt)
      exact max_le (le_refl _) hle
    calc P.natDegree • d z = d (Polynomial.aeval z P - Polynomial.aeval z P.eraseLead) :=
          hstep2
      _ ≤ max (d (Polynomial.aeval z P)) (d (Polynomial.aeval z P.eraseLead)) := hstep1
      _ ≤ max (d (Polynomial.aeval z P)) ((P.natDegree - 1) • d z) := hstep3
      _ ≤ d (Polynomial.aeval z P) := hstep4

/-! ## The sign automorphism and generator extensionality -/

/-- The affine involution on `F[X,Y]` is an involution. -/
theorem affineInvolution_comp :
    S2482AffineInvolutionAlgHom.comp S2482AffineInvolutionAlgHom =
      AlgHom.id F (MvPolynomial (Fin 2) F) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [S2482AffineInvolutionAlgHom]
  · simp [S2482AffineInvolutionAlgHom]

/-- The sign involution on the coordinate ring is an involution. -/
theorem sigmaR_comp :
    S2482CoordinateRingInvolution.comp S2482CoordinateRingInvolution =
      AlgHom.id F S2482CoordinateRing := by
  have hmk : ∀ q : MvPolynomial (Fin 2) F,
      S2482CoordinateRingInvolution (Ideal.Quotient.mk _ q) =
        Ideal.Quotient.mk _ (S2482AffineInvolutionAlgHom q) := by
    intro q
    rfl
  apply AlgHom.ext
  intro z
  induction z using Quotient.inductionOn' with
  | _ q =>
    have hq : S2482AffineInvolutionAlgHom (S2482AffineInvolutionAlgHom q) = q := by
      have := congrFun (congrArg DFunLike.coe affineInvolution_comp) q
      simpa using this
    show S2482CoordinateRingInvolution
      (S2482CoordinateRingInvolution (Ideal.Quotient.mk _ q)) = Ideal.Quotient.mk _ q
    rw [hmk, hmk, hq]

/-- The sign involution as an algebra equivalence. -/
noncomputable def sigmaRE : S2482CoordinateRing ≃ₐ[F] S2482CoordinateRing :=
  AlgEquiv.ofAlgHom S2482CoordinateRingInvolution S2482CoordinateRingInvolution
    sigmaR_comp sigmaR_comp

@[simp]
theorem sigmaRE_toAlgHom :
    sigmaRE.toAlgHom = S2482CoordinateRingInvolution := rfl

theorem sigmaR_x : S2482CoordinateRingInvolution
    (Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 0)) =
    Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 0) := by
  simp [S2482CoordinateRingInvolution, S2482AffineInvolutionAlgHom]

theorem sigmaR_y : S2482CoordinateRingInvolution
    (Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 1)) =
    -(Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 1)) := by
  simp [S2482CoordinateRingInvolution, S2482AffineInvolutionAlgHom]

/-- The sign automorphism of `A`, conjugated from the sign involution on `R`. -/
noncomputable def signA : A ≃ₐ[F] A :=
  e.symm.trans (sigmaRE.trans e)

theorem signA_xC : signA xC = xC := by
  rw [signA, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  have hx : e.symm xC =
      Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 0) := by
    rw [← e_x, AlgEquiv.symm_apply_apply]
  rw [hx]
  change e (S2482CoordinateRingInvolution
    (Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 0))) = xC
  rw [sigmaR_x, e_x]

theorem signA_yC : signA yC = -yC := by
  rw [signA, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  have hy : e.symm yC =
      Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 1) := by
    rw [← e_y, AlgEquiv.symm_apply_apply]
  rw [hy]
  change e (S2482CoordinateRingInvolution
    (Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 1))) = -yC
  rw [sigmaR_y, map_neg, e_y]

/-- Two `F`-algebra homs out of `A` agreeing on `x` and `y` are equal. -/
theorem algHom_ext_generators {B : Type*} [Semiring B] [Algebra F B] (f g : A →ₐ[F] B)
    (hx : f xC = g xC) (hy : f yC = g yC) : f = g := by
  apply AlgHom.ext
  intro z
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq z
  have hmap : ∀ (h : A →ₐ[F] B) (p q : Polynomial F),
      h (p • (1 : A) + q • yC) =
        Polynomial.aeval (h xC) p + Polynomial.aeval (h xC) q * h yC := by
    intro h p q
    have h1 : h (p • (1 : A)) = Polynomial.aeval (h xC) p := by
      rw [smul_one_eq_aeval, Polynomial.aeval_algHom_apply]
    have h2 : h (q • yC) = Polynomial.aeval (h xC) q * h yC := by
      rw [Algebra.smul_def, map_mul, Algebra.algebraMap_eq_smul_one,
        smul_one_eq_aeval, Polynomial.aeval_algHom_apply]
    rw [map_add, h1, h2]
  change f (p • (1 : A) + q • yC) = g (p • (1 : A) + q • yC)
  rw [hmap f, hmap g, hx, hy]

/-! ## Status

The infrastructure above proves:
* the degree function `d` on the affine coordinate ring `A = F[X,Y]/(Y^2-X^3+X)`,
  with multiplicativity `d_mul`, powers `d_pow`, subadditivity `d_add_le`,
  the coordinate formula `d_smul_basis`, `d xC = 2`, `d yC = 3`, strict monotonicity
  `nsmul_lt_nsmul_of_pos`, the polynomial bounds `d_aeval_le_of_le` and `d_aeval_ge`;
* the sign automorphism `signA` on `A`, its action `signA xC = xC`, `signA yC = -yC`;
* generator extensionality `algHom_ext_generators` for `F`-algebra homs out of `A`.

The remaining gap to `S2482OrderTwoAlgAutClassification` is the actual order-two
analysis: for `psi : A ~=+* A` with `psi^2 = id`, put `a = psi xC`, `b = psi yC`.
The missing steps are, in order:
1. `b^2 = a^3 - a` and the degree computation giving `d a = 2n`, `d b = 3n`
   (needs `d(a^3-a) = 3 d a`, provable from `d_add_le` by the reverse-triangle
   argument, and `d a != 0`, which follows from `a` not being in the image of `F`);
2. the even-degree normal-form analysis `max_even_analysis` (degree of `P` is `n`,
   `q = 0` or `deg q + 2 <= n`), and the inequalities giving `n = 1`;
3. with `d a = 2`, `d b = 3`, the normal forms `a = c xC + d0`, `b = e yC + R(xC)`;
   the equation `b^2 = a^3 - a` then forces `R = 0`, and comparing coefficients in
   `e^2 (X^3-X) = (cX+d0)^3 - (cX+d0)` forces `c = 1`, `e = +-1`;
4. transfer to `S2482CoordinateRing` along the algebra equivalence `e` and conclude
   `phi = id` or `phi.toAlgHom = S2482CoordinateRingInvolution`.

No `sorry`, `axiom` or fake inhabitant is used in this file.  The target
`S2482OrderTwoAlgAutClassification` is *not* proved here.
-/

end LeanFormal.IUT.XiFPaper.S2482OrderTwoAlgAutClassificationActualV3

end