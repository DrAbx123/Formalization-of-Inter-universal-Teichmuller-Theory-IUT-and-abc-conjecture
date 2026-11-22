import tmp.sheaf.xif.paper.S2482QiNontrivialActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Bivariate

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.XiFPaper.S2482OrderTwoAlgAutClassificationActual

open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2482QiNontrivialActual

/-- The Weierstrass curve y^2 = x^3 - x as an affine Weierstrass curve over F. -/
abbrev W : WeierstrassCurve F := S2482Curve

/-- Mathlib's affine coordinate ring of W, i.e. F[X,Y]/(Y^2 - X^3 + X). -/
abbrev Coord : Type := WeierstrassCurve.Affine.CoordinateRing W

/-- The class of X in the coordinate ring. -/
noncomputable def xC : Coord :=
  WeierstrassCurve.Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.X : Polynomial F))

/-- The class of Y in the coordinate ring. -/
noncomputable def yC : Coord :=
  WeierstrassCurve.Affine.CoordinateRing.mk W (Polynomial.X : Polynomial (Polynomial F))

instance instFreeCoord : Module.Free (Polynomial F) Coord :=
  Module.Free.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W)

instance instFiniteCoord : Module.Finite (Polynomial F) Coord :=
  Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W)

theorem polynomial_W : WeierstrassCurve.Affine.polynomial W =
    (Polynomial.X : Polynomial (Polynomial F)) ^ 2 -
      Polynomial.C ((Polynomial.X : Polynomial F) ^ 3 - Polynomial.X) := by
  simp [WeierstrassCurve.Affine.polynomial, W, S2482Curve, sub_eq_add_neg]

theorem yC_sq : yC ^ 2 = xC ^ 3 - xC := by
  have h : (AdjoinRoot.mk (WeierstrassCurve.Affine.polynomial W))
      ((Polynomial.X : Polynomial (Polynomial F)) ^ 2 -
        Polynomial.C ((Polynomial.X : Polynomial F) ^ 3 - Polynomial.X)) = 0 := by
    rw [← polynomial_W]
    exact AdjoinRoot.mk_self
  have h' : yC ^ 2 - (xC ^ 3 - xC) = 0 := by
    simpa [yC, xC, map_sub, map_pow] using h
  linear_combination h'

/-- The defining ideal of the S2482 coordinate ring. -/
abbrev Icurve : Ideal (MvPolynomial (Fin 2) F) := Ideal.span {S2482AffinePolynomial}

/-- The class of x in S2482CoordinateRing. -/
noncomputable def xR : S2482CoordinateRing := Ideal.Quotient.mk Icurve (MvPolynomial.X 0)

/-- The class of y in S2482CoordinateRing. -/
noncomputable def yR : S2482CoordinateRing := Ideal.Quotient.mk Icurve (MvPolynomial.X 1)

theorem yR_sq : yR ^ 2 = xR ^ 3 - xR := by
  have hmem : S2482AffinePolynomial ∈ Icurve := Ideal.subset_span (Set.mem_singleton _)
  have hzero : Ideal.Quotient.mk Icurve S2482AffinePolynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have h : yR ^ 2 - (xR ^ 3 + -xR) = 0 := by
    simpa [xR, yR, S2482AffinePolynomial,
      LeanFormal.IUT.IUTII.Frobenioid.Example36.weierstrassAffinePolynomial,
      S2482Curve, map_add, map_sub, map_pow] using hzero
  linear_combination h

theorem equivMvPolynomial_W_polynomial :
    Polynomial.Bivariate.equivMvPolynomial F
      (WeierstrassCurve.Affine.polynomial W) = S2482AffinePolynomial := by
  rw [polynomial_W]
  simp [S2482AffinePolynomial,
    LeanFormal.IUT.IUTII.Frobenioid.Example36.weierstrassAffinePolynomial, S2482Curve,
    sub_eq_add_neg]

theorem map_ideal_eq :
    Ideal.span {WeierstrassCurve.Affine.polynomial W} =
      Ideal.map (↑(Polynomial.Bivariate.equivMvPolynomial F).symm :
        MvPolynomial (Fin 2) F →+* Polynomial (Polynomial F)) Icurve := by
  rw [Icurve, Ideal.map_span, Set.image_singleton]
  have hf : (↑(Polynomial.Bivariate.equivMvPolynomial F).symm :
      MvPolynomial (Fin 2) F →+* Polynomial (Polynomial F)) S2482AffinePolynomial =
      WeierstrassCurve.Affine.polynomial W := by
    rw [← equivMvPolynomial_W_polynomial]
    exact AlgEquiv.symm_apply_apply (Polynomial.Bivariate.equivMvPolynomial F)
      (WeierstrassCurve.Affine.polynomial W)
  rw [hf]

/-- The F-algebra identification between S2482CoordinateRing and Mathlib's
affine coordinate ring of y^2 = x^3 - x. -/
noncomputable def e : S2482CoordinateRing ≃ₐ[F] Coord :=
  Ideal.quotientEquivAlg (I := Icurve)
    (J := Ideal.span {WeierstrassCurve.Affine.polynomial W})
    (Polynomial.Bivariate.equivMvPolynomial F).symm map_ideal_eq

theorem e_xR : e xR = xC := by
  change Ideal.Quotient.mk (Ideal.span {WeierstrassCurve.Affine.polynomial W})
      ((Polynomial.Bivariate.equivMvPolynomial F).symm (MvPolynomial.X 0)) = xC
  rw [Polynomial.Bivariate.equivMvPolynomial_symm_X_0]
  rfl

theorem e_yR : e yR = yC := by
  change Ideal.Quotient.mk (Ideal.span {WeierstrassCurve.Affine.polynomial W})
      ((Polynomial.Bivariate.equivMvPolynomial F).symm (MvPolynomial.X 1)) = yC
  rw [Polynomial.Bivariate.equivMvPolynomial_symm_X_1]
  rfl

/-! ## The norm-degree function -/

/-- Degree of the algebra norm to F[X]; a substitute for the pole order at infinity. -/
noncomputable def deg (z : Coord) : WithBot ℕ := (Algebra.norm (Polynomial F) z).degree

theorem deg_smul_basis_mk (p q : Polynomial F) :
    deg (p • (1 : Coord) + q • (WeierstrassCurve.Affine.CoordinateRing.mk W)
      (Polynomial.X : Polynomial (Polynomial F))) =
      max (2 • p.degree) (2 • q.degree + 3) := by
  rw [deg, WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis]

theorem deg_smul_basis (p q : Polynomial F) :
    deg (p • (1 : Coord) + q • yC) = max (2 • p.degree) (2 • q.degree + 3) := by
  simpa only [yC] using deg_smul_basis_mk p q

theorem deg_eq_bot_iff {z : Coord} : deg z = ⊥ ↔ z = 0 := by
  rw [deg, Polynomial.degree_eq_bot, Algebra.norm_eq_zero_iff]

theorem deg_zero : deg (0 : Coord) = ⊥ := by
  rw [deg, Algebra.norm_zero, Polynomial.degree_zero]

theorem deg_mul (z w : Coord) : deg (z * w) = deg z + deg w := by
  simp only [deg, map_mul, Polynomial.degree_mul]

theorem deg_one : deg (1 : Coord) = 0 := by
  simp [deg]

theorem deg_pow (z : Coord) (n : ℕ) : deg (z ^ n) = n • deg z := by
  induction n with
  | zero => simp [deg_one]
  | succ n ih => rw [pow_succ, deg_mul, ih, succ_nsmul]

theorem two_nsmul_max (x y : WithBot ℕ) :
    (2 : ℕ) • max x y = max (2 • x) (2 • y) := by
  apply le_antisymm
  · rcases max_cases x y with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; exact le_max_left _ _
    · rw [h]; exact le_max_right _ _
  · apply max_le
    · rw [two_nsmul, two_nsmul]
      exact add_le_add (le_max_left _ _) (le_max_left _ _)
    · rw [two_nsmul, two_nsmul]
      exact add_le_add (le_max_right _ _) (le_max_right _ _)

theorem max_add_three (x y : WithBot ℕ) : max x y + 3 = max (x + 3) (y + 3) := by
  apply le_antisymm
  · rcases max_cases x y with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; exact le_max_left _ _
    · rw [h]; exact le_max_right _ _
  · exact max_le (add_le_add_left (le_max_left _ _) 3)
      (add_le_add_left (le_max_right _ _) 3)

theorem deg_neg (z : Coord) : deg (-z) = deg z := by
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq z
  have hneg : -(p • (1 : Coord) + q • (WeierstrassCurve.Affine.CoordinateRing.mk W)
      (Polynomial.X : Polynomial (Polynomial F))) =
      (-p) • (1 : Coord) + (-q) • (WeierstrassCurve.Affine.CoordinateRing.mk W)
        (Polynomial.X : Polynomial (Polynomial F)) := by
    module
  rw [hneg, deg_smul_basis_mk, deg_smul_basis_mk]
  simp [Polynomial.degree_neg]

theorem deg_add_le (z w : Coord) : deg (z + w) ≤ max (deg z) (deg w) := by
  obtain ⟨p1, q1, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq z
  obtain ⟨p2, q2, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq w
  have hsum : p1 • (1 : Coord) + q1 • (WeierstrassCurve.Affine.CoordinateRing.mk W)
        (Polynomial.X : Polynomial (Polynomial F)) +
      (p2 • (1 : Coord) + q2 • (WeierstrassCurve.Affine.CoordinateRing.mk W)
        (Polynomial.X : Polynomial (Polynomial F))) =
      (p1 + p2) • (1 : Coord) + (q1 + q2) • (WeierstrassCurve.Affine.CoordinateRing.mk W)
        (Polynomial.X : Polynomial (Polynomial F)) := by
    module
  rw [hsum, deg_smul_basis_mk, deg_smul_basis_mk, deg_smul_basis_mk]
  have hp : (p1 + p2).degree ≤ max p1.degree p2.degree := Polynomial.degree_add_le _ _
  have hq : (q1 + q2).degree ≤ max q1.degree q2.degree := Polynomial.degree_add_le _ _
  have h2 : 2 • (p1 + p2).degree ≤ max (2 • p1.degree) (2 • p2.degree) := by
    calc 2 • (p1 + p2).degree ≤ 2 • max p1.degree p2.degree := by gcongr
      _ = max (2 • p1.degree) (2 • p2.degree) := two_nsmul_max _ _
  have h3 : 2 • (q1 + q2).degree + 3 ≤
      max (2 • q1.degree + 3) (2 • q2.degree + 3) := by
    calc 2 • (q1 + q2).degree + 3 ≤ 2 • max q1.degree q2.degree + 3 := by gcongr
      _ = max (2 • q1.degree + 3) (2 • q2.degree + 3) := by
        rw [two_nsmul_max, max_add_three]
  calc max (2 • (p1 + p2).degree) (2 • (q1 + q2).degree + 3)
      ≤ max (max (2 • p1.degree) (2 • p2.degree))
          (max (2 • q1.degree + 3) (2 • q2.degree + 3)) :=
        max_le (h2.trans (le_max_left _ _)) (h3.trans (le_max_right _ _))
    _ = max (max (2 • p1.degree) (2 • q1.degree + 3))
          (max (2 • p2.degree) (2 • q2.degree + 3)) := by ac_rfl

theorem deg_add_eq_of_lt {z w : Coord} (h : deg z < deg w) : deg (z + w) = deg w := by
  have h1 : deg (z + w) ≤ deg w := by
    have hle := deg_add_le z w
    rwa [max_eq_right h.le] at hle
  rcases lt_or_eq_of_le h1 with hlt | heq
  · exfalso
    have h3 : deg w ≤ max (deg (z + w)) (deg z) := by
      have hsub := deg_add_le (z + w) (-z)
      rw [show z + w + -z = w by ring, deg_neg] at hsub
      exact hsub
    have hmax : max (deg (z + w)) (deg z) < deg w := max_lt hlt h
    exact (not_lt_of_ge h3) hmax
  · exact heq

theorem nsmul_coe (a k : ℕ) : a • (↑k : WithBot ℕ) = ↑(a * k) := by
  have h := WithBot.coe_nsmul (α := ℕ) k a
  rw [Nat.nsmul_eq_mul] at h
  exact h.symm

theorem deg_algebraMap {c : F} (hc : c ≠ 0) : deg (algebraMap F Coord c) = 0 := by
  have h : algebraMap F Coord c = (Polynomial.C c) • (1 : Coord) + (0 : Polynomial F) • yC := by
    rw [zero_smul, add_zero, Algebra.smul_def, mul_one]
    rw [IsScalarTower.algebraMap_apply F (Polynomial F) Coord c, Polynomial.C_eq_algebraMap]
  rw [h, deg_smul_basis]
  simp [hc]

theorem deg_eq_zero_iff {z : Coord} :
    deg z = 0 ↔ ∃ c : F, c ≠ 0 ∧ z = algebraMap F Coord c := by
  constructor
  · intro hz
    obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq z
    rw [deg_smul_basis_mk] at hz
    have hq : q = 0 := by
      by_contra hq
      have hB : 2 • q.degree + 3 = ↑(2 * q.natDegree + 3) := by
        rw [Polynomial.degree_eq_natDegree hq, nsmul_coe]
        exact (WithBot.coe_add (α := ℕ) (2 * q.natDegree) 3).symm
      have hBge : (3 : WithBot ℕ) ≤ 2 • q.degree + 3 := by
        rw [hB]
        exact (WithBot.coe_le_coe (α := ℕ) (a := 3) (b := 2 * q.natDegree + 3)).mpr (by omega)
      have hle : 2 • q.degree + 3 ≤ 0 := by
        rw [← hz]
        exact le_max_right _ _
      have h30 : (3 : WithBot ℕ) ≤ 0 := hBge.trans hle
      exact absurd h30 (by norm_num)
    subst q
    have hz' : 2 • p.degree = 0 := by
      simpa using hz
    have hp : p ≠ 0 := by
      intro hp
      rw [hp, Polynomial.degree_zero] at hz'
      simp at hz'
    have hk : p.natDegree = 0 := by
      have hpd : p.degree = ↑p.natDegree := Polynomial.degree_eq_natDegree hp
      rw [hpd, nsmul_coe] at hz'
      have h2 : 2 * p.natDegree = 0 := by
        have h0 : (0 : WithBot ℕ) = ↑(0 : ℕ) := rfl
        rw [h0] at hz'
        exact (WithBot.coe_inj (α := ℕ)).mp hz'
      omega
    let c0 : F := p.coeff 0
    have hpC : p = Polynomial.C c0 := Polynomial.eq_C_of_natDegree_eq_zero hk
    refine ⟨c0, ?_, ?_⟩
    · intro hc
      apply hp
      rw [hpC, hc, Polynomial.C_0]
    · rw [hpC, zero_smul, add_zero, Algebra.smul_def, mul_one]
      rw [Polynomial.C_eq_algebraMap,
        IsScalarTower.algebraMap_apply F (Polynomial F) Coord c0]
  · rintro ⟨c, hc, hz⟩
    rw [hz]
    exact deg_algebraMap hc

theorem deg_pos_exists {x : WithBot ℕ} (hx : 0 < x) : ∃ k : ℕ, 0 < k ∧ x = ↑k := by
  have hxne : x ≠ ⊥ := by
    rintro rfl
    simp at hx
  obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hxne
  refine ⟨n, ?_, hn.symm⟩
  have hx' : (0 : WithBot ℕ) < ↑n := by rw [← hn] at hx; exact hx
  exact (WithBot.coe_lt_coe (α := ℕ) (a := 0) (b := n)).mp hx'

theorem lt_nsmul_of_pos {k : ℕ} (hk : 0 < k) {a b : ℕ} (h : a < b) :
    a • (↑k : WithBot ℕ) < b • (↑k : WithBot ℕ) := by
  calc a • (↑k : WithBot ℕ) = ↑(a * k) := nsmul_coe a k
    _ < ↑(b * k) := (WithBot.coe_lt_coe (α := ℕ) (a := a * k) (b := b * k)).mpr
        (Nat.mul_lt_mul_of_pos_right h hk)
    _ = b • (↑k : WithBot ℕ) := (nsmul_coe b k).symm

theorem bot_lt_nsmul {m k : ℕ} (hk : 0 < k) :
    (⊥ : WithBot ℕ) < m • (↑k : WithBot ℕ) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simpa using WithBot.bot_lt_coe (0 : ℕ)
  · exact WithBot.bot_lt_coe _

theorem deg_aeval_of_ne_zero (u : Coord) (hu : 0 < deg u)
    (a : Polynomial F) (ha : a ≠ 0) :
    deg (Polynomial.aeval u a) = a.natDegree • deg u := by
  obtain ⟨k, hkpos, hk⟩ := deg_pos_exists hu
  have H : ∀ m : ℕ, ∀ a : Polynomial F, a.natDegree = m → a ≠ 0 →
      deg (Polynomial.aeval u a) = a.natDegree • deg u := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro a ha hane
      have hc : a.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hane
      have hdecomp : a = Polynomial.C a.leadingCoeff * Polynomial.X ^ m + a.eraseLead := by
        have h := Polynomial.eraseLead_add_C_mul_X_pow a
        rw [ha] at h
        exact h.symm.trans (add_comm _ _)
      have haeval : Polynomial.aeval u a =
          algebraMap F Coord a.leadingCoeff * u ^ m + Polynomial.aeval u a.eraseLead := by
        conv_lhs => rw [hdecomp]
        rw [map_add, map_mul, map_pow]
        simp
      have hterm : deg (algebraMap F Coord a.leadingCoeff * u ^ m) = m • deg u := by
        rw [deg_mul, deg_pow, deg_algebraMap hc]
        simp
      have hrlt : deg (Polynomial.aeval u a.eraseLead) < m • deg u := by
        rcases eq_or_ne a.eraseLead 0 with hzero | hrne
        · rw [hzero, Polynomial.aeval_zero, deg_zero]
          simpa [hk] using bot_lt_nsmul (m := m) hkpos
        · have hrn : (a.eraseLead).natDegree < m := by
            rcases Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero a with h | h
            · rwa [ha] at h
            · exact absurd h hrne
          have hih := ih (a.eraseLead).natDegree hrn a.eraseLead rfl hrne
          rw [hih]
          simpa [hk] using lt_nsmul_of_pos hkpos hrn
      have hlt : deg (Polynomial.aeval u a.eraseLead) <
          deg (algebraMap F Coord a.leadingCoeff * u ^ m) := by
        rw [hterm]; exact hrlt
      rw [haeval, add_comm, deg_add_eq_of_lt hlt, hterm, ha]
  exact H a.natDegree a rfl ha

theorem deg_xC : deg xC = 2 := by
  have h : xC = (Polynomial.X : Polynomial F) • (1 : Coord) + (0 : Polynomial F) • yC := by
    rw [zero_smul, add_zero, Algebra.smul_def, mul_one]
    rfl
  rw [h, deg_smul_basis]
  simp

theorem deg_yC : deg yC = 3 := by
  have h : yC = (0 : Polynomial F) • (1 : Coord) + (1 : Polynomial F) • yC := by
    simp
  rw [h, deg_smul_basis]
  simp

theorem xC_ne_zero : xC ≠ 0 := by
  intro h
  have h2 := deg_xC
  rw [h, deg_zero] at h2
  exact (by norm_num : (⊥ : WithBot ℕ) ≠ 2) h2

theorem yC_ne_zero : yC ≠ 0 := by
  intro h
  have h2 := deg_yC
  rw [h, deg_zero] at h2
  exact (by norm_num : (⊥ : WithBot ℕ) ≠ 3) h2

theorem smul_one_eq_aeval (p : Polynomial F) :
    p • (1 : Coord) = Polynomial.aeval xC p := by
  rw [Algebra.smul_def, mul_one]
  have h : (Polynomial.aeval xC : Polynomial F →ₐ[F] Coord) =
      IsScalarTower.toAlgHom F (Polynomial F) Coord := by
    apply Polynomial.algHom_ext
    simp [xC]
  exact (congrArg (fun f => f p) h).symm

theorem algebraMap_injective : Function.Injective (algebraMap (Polynomial F) Coord) :=
  AdjoinRoot.of.injective_of_degree_ne_zero (by
    rw [WeierstrassCurve.Affine.degree_polynomial]
    norm_num)

theorem xC_ne_algebraMap (c : F) : xC ≠ algebraMap F Coord c := by
  intro hc
  have hzero : (AdjoinRoot.mk (WeierstrassCurve.Affine.polynomial W))
      (Polynomial.C ((Polynomial.X : Polynomial F) - Polynomial.C c)) = 0 := by
    have hsub : (Polynomial.C ((Polynomial.X : Polynomial F) - Polynomial.C c) :
        Polynomial (Polynomial F)) = Polynomial.C (Polynomial.X : Polynomial F) -
          Polynomial.C (Polynomial.C c) := by simp
    rw [hsub, map_sub]
    change xC - algebraMap F Coord c = 0
    rw [hc, sub_self]
  have hne := AdjoinRoot.mk_ne_zero_of_natDegree_lt
    (WeierstrassCurve.Affine.monic_polynomial (W := W))
    (Polynomial.C_ne_zero.mpr (Polynomial.X_sub_C_ne_zero c)) ?_
  · exact hne hzero
  · rw [Polynomial.natDegree_C, WeierstrassCurve.Affine.natDegree_polynomial]
    norm_num

/-- The sign automorphism x -> x, y -> -y of the coordinate ring. -/
theorem signC_eval :
    (WeierstrassCurve.Affine.polynomial W).eval₂
      (IsScalarTower.toAlgHom F (Polynomial F) Coord) (-yC) = 0 := by
  conv_lhs => arg 3; rw [polynomial_W]
  simp [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, IsScalarTower.toAlgHom, xC, yC_sq]

noncomputable def signC : Coord →ₐ[F] Coord :=
  AdjoinRoot.liftAlgHom (WeierstrassCurve.Affine.polynomial W)
    (IsScalarTower.toAlgHom F (Polynomial F) Coord) (-yC) signC_eval

theorem signC_xC : signC xC = xC := by
  rw [signC]
  change AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.mk _ (Polynomial.C (Polynomial.X : Polynomial F))) = xC
  rw [AdjoinRoot.liftAlgHom_mk]
  simp [xC, IsScalarTower.toAlgHom]

theorem signC_yC : signC yC = -yC := by
  rw [signC]
  have h := AdjoinRoot.liftAlgHom_root (WeierstrassCurve.Affine.polynomial W)
    (IsScalarTower.toAlgHom F (Polynomial F) Coord) (-yC) signC_eval
  simpa [yC] using h

theorem signC_algebraMap (r : Polynomial F) :
    signC (algebraMap (Polynomial F) Coord r) = algebraMap (Polynomial F) Coord r := by
  rw [signC]
  change AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.mk _ (Polynomial.C r)) =
    algebraMap (Polynomial F) Coord r
  rw [AdjoinRoot.liftAlgHom_mk, Polynomial.eval₂_C]
  rfl

theorem signC_smul (r : Polynomial F) (z : Coord) :
    signC (r • z) = r • signC z := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, signC_algebraMap r]

theorem xC_aeval_eq_algebraMap (r : Polynomial F) :
    Polynomial.aeval xC r = algebraMap (Polynomial F) Coord r := by
  rw [← smul_one_eq_aeval r, Algebra.smul_def, mul_one]

theorem algebraMap_F_injective : Function.Injective (algebraMap F Coord) :=
  FaithfulSMul.algebraMap_injective F Coord

/-- An order-two algebra automorphism of the affine coordinate ring of `y^2 = x^3 - x`
fixes `x` and sends `y` to `±y`. -/
theorem orderTwo_fixes (ψ : Coord ≃ₐ[F] Coord)
    (hψ : ψ.toAlgHom.comp ψ.toAlgHom = AlgHom.id F Coord) :
    ψ xC = xC ∧ (ψ yC = yC ∨ ψ yC = -yC) := by
  have hψx : ψ (ψ xC) = xC := by
    have h := congrArg (fun f : Coord →ₐ[F] Coord => f xC) hψ
    simpa [AlgHom.comp_apply] using h
  have hψy : ψ (ψ yC) = yC := by
    have h := congrArg (fun f : Coord →ₐ[F] Coord => f yC) hψ
    simpa [AlgHom.comp_apply] using h
  set u : Coord := ψ xC with hu
  set v : Coord := ψ yC with hv
  have hψu : ψ u = xC := by simpa [hu] using hψx
  have hψv : ψ v = yC := by simpa [hv] using hψy
  have hv_sq : v ^ 2 = u ^ 3 - u := by
    have h := congrArg ψ yC_sq
    simpa [← hu, ← hv, map_pow, map_sub] using h
  have hu_ne : u ≠ 0 := by
    intro h0
    have : xC = 0 := by rw [← hψu, h0, map_zero]
    exact xC_ne_zero this
  have hv_ne : v ≠ 0 := by
    intro h0
    have : yC = 0 := by rw [← hψv, h0, map_zero]
    exact yC_ne_zero this
  have hdeg_u_ne_zero : deg u ≠ 0 := by
    intro h0
    obtain ⟨c, hc, huc⟩ := deg_eq_zero_iff.mp h0
    apply xC_ne_algebraMap c
    rw [← hψu, huc]
    exact ψ.commutes c
  have hu_pos : 0 < deg u := by
    rcases lt_or_gt_of_ne (Ne.symm hdeg_u_ne_zero) with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := WithBot.ne_bot_iff_exists.mp (by
        intro hbot
        exact hu_ne ((deg_eq_bot_iff).mp hbot))
      rw [← hk] at h
      simp at h
  obtain ⟨n, hnpos, hn⟩ := deg_pos_exists hu_pos
  have hdu3 : deg (u ^ 3 - u) = (3 : ℕ) • deg u := by
    have h3 : deg (u ^ 3) = (3 : ℕ) • deg u := deg_pow u 3
    have hlt : deg (-u) < deg (u ^ 3) := by
      rw [deg_neg, h3, hn, nsmul_coe]
      exact (WithBot.coe_lt_coe (α := ℕ) (a := n) (b := 3 * n)).mpr (by omega)
    rw [sub_eq_add_neg, add_comm, deg_add_eq_of_lt hlt, h3]
  have hEq : (2 : ℕ) • deg v = (3 : ℕ) • deg u := by
    calc (2 : ℕ) • deg v = deg (v ^ 2) := (deg_pow v 2).symm
      _ = deg (u ^ 3 - u) := by rw [hv_sq]
      _ = (3 : ℕ) • deg u := hdu3
  have hv_ne_bot : deg v ≠ ⊥ := by
    intro hbot
    exact hv_ne ((deg_eq_bot_iff).mp hbot)
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hv_ne_bot
  have hEq2 : 2 * m = 3 * n := by
    have h := hEq
    rw [← hm, hn] at h
    have h' : (↑(2 * m) : WithBot ℕ) = (↑(3 * n) : WithBot ℕ) := by
      calc (↑(2 * m) : WithBot ℕ) = (2 : ℕ) • (↑m : WithBot ℕ) := (nsmul_coe 2 m).symm
        _ = (3 : ℕ) • (↑n : WithBot ℕ) := h
        _ = (↑(3 * n) : WithBot ℕ) := nsmul_coe 3 n
    exact (WithBot.coe_inj (α := ℕ)).mp h'
  obtain ⟨kk, hnk, hmk⟩ : ∃ kk : ℕ, n = 2 * kk ∧ m = 3 * kk := by
    refine ⟨m - n, by omega, by omega⟩
  have hkkpos : 0 < kk := by omega
  have hdu : deg u = (↑(2 * kk) : WithBot ℕ) := by rw [hn, hnk]
  have hdv : deg v = (↑(3 * kk) : WithBot ℕ) := by rw [← hm, hmk]; rfl
  obtain ⟨p, q, hu_eq⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq u
  have hcoord : max (2 • p.degree) (2 • q.degree + 3) = (↑(2 * kk) : WithBot ℕ) := by
    rw [← deg_smul_basis_mk p q, hu_eq, hdu]
  have hA_le : 2 • p.degree ≤ (↑(2 * kk) : WithBot ℕ) := by
    rw [← hcoord]; exact le_max_left _ _
  have hBval_of_ne {r : Polynomial F} (hr : r ≠ 0) :
      2 • r.degree + 3 = (↑(2 * r.natDegree + 3) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hr, nsmul_coe]
    exact (WithBot.coe_add (α := ℕ) (2 * r.natDegree) 3).symm
  have hA_eq : 2 • p.degree = (↑(2 * kk) : WithBot ℕ) := by
    rcases lt_or_eq_of_le hA_le with hlt | heq
    · exfalso
      have hB_le : 2 • q.degree + 3 ≤ (↑(2 * kk) : WithBot ℕ) := by
        rw [← hcoord]; exact le_max_right _ _
      have hB_eq : 2 • q.degree + 3 = (↑(2 * kk) : WithBot ℕ) := by
        by_contra hne
        have hBlt : 2 • q.degree + 3 < (↑(2 * kk) : WithBot ℕ) :=
          lt_of_le_of_ne hB_le hne
        have hmaxlt : max (2 • p.degree) (2 • q.degree + 3) < (↑(2 * kk) : WithBot ℕ) :=
          max_lt hlt hBlt
        rw [hcoord] at hmaxlt
        exact lt_irrefl _ hmaxlt
      rcases eq_or_ne q 0 with hq0 | hqne
      · rw [hq0, Polynomial.degree_zero, two_nsmul, WithBot.bot_add, WithBot.bot_add] at hB_eq
        have hne : (↑(2 * kk) : WithBot ℕ) ≠ ⊥ := WithBot.coe_ne_bot
        exact hne hB_eq.symm
      · rw [hBval_of_ne hqne] at hB_eq
        have hnum : 2 * q.natDegree + 3 = 2 * kk := (WithBot.coe_inj (α := ℕ)).mp hB_eq
        omega
    · exact heq
  have hpne : p ≠ 0 := by
    intro hp0
    rw [hp0, Polynomial.degree_zero, two_nsmul, WithBot.bot_add] at hA_eq
    have hne : (↑(2 * kk) : WithBot ℕ) ≠ ⊥ := WithBot.coe_ne_bot
    exact hne hA_eq.symm
  have hpk : p.natDegree = kk := by
    rw [Polynomial.degree_eq_natDegree hpne, nsmul_coe] at hA_eq
    have h2 : 2 * p.natDegree = 2 * kk := (WithBot.coe_inj (α := ℕ)).mp hA_eq
    omega
  have hqY : q • ((WeierstrassCurve.Affine.CoordinateRing.mk W)
        (Polynomial.X : Polynomial (Polynomial F))) = Polynomial.aeval xC q * yC := by
    rw [show q • ((WeierstrassCurve.Affine.CoordinateRing.mk W)
        (Polynomial.X : Polynomial (Polynomial F))) = q • yC from rfl]
    rw [Algebra.smul_def]
    rw [show algebraMap (Polynomial F) Coord q = Polynomial.aeval xC q from by
      rw [← smul_one_eq_aeval q, Algebra.smul_def, mul_one]]
  have hψ_aeval (r : Polynomial F) : ψ (Polynomial.aeval xC r) = Polynomial.aeval u r :=
    (Polynomial.aeval_algHom_apply ψ xC r).symm
  have hψu_eq : ψ u = Polynomial.aeval u p + Polynomial.aeval u q * v := by
    conv_lhs => rw [← hu_eq]
    rw [map_add, smul_one_eq_aeval p, hqY, map_mul, hψ_aeval p, hψ_aeval q, ← hv]
  have hAdeg : deg (Polynomial.aeval u p) = (↑(2 * kk * kk) : WithBot ℕ) := by
    rw [deg_aeval_of_ne_zero u hu_pos p hpne, hpk, hdu, nsmul_coe]
    congr 1
    ring
  have hBdeg {hq : q ≠ 0} :
      deg (Polynomial.aeval u q * v) = (↑(kk * (2 * q.natDegree + 3)) : WithBot ℕ) := by
    rw [deg_mul, deg_aeval_of_ne_zero u hu_pos q hq, hdu, hdv]
    calc q.natDegree • (↑(2 * kk) : WithBot ℕ) + (↑(3 * kk) : WithBot ℕ)
        = (↑(q.natDegree * (2 * kk)) : WithBot ℕ) + (↑(3 * kk) : WithBot ℕ) := by
          rw [nsmul_coe]
      _ = (↑(q.natDegree * (2 * kk) + 3 * kk) : WithBot ℕ) :=
          (WithBot.coe_add (α := ℕ) _ _).symm
      _ = (↑(kk * (2 * q.natDegree + 3)) : WithBot ℕ) := by
          congr 1
          ring
  have hkey : (2 : WithBot ℕ) = (↑(2 * kk * kk) : WithBot ℕ) := by
    rcases eq_or_ne q 0 with hq0 | hqne
    · have hψu_simp : ψ u = Polynomial.aeval u p := by
        rw [hψu_eq, hq0]
        simp
      have hx2 : deg (Polynomial.aeval u p) = 2 := by
        rw [← hψu_simp, hψx, deg_xC]
      rw [← hx2, hAdeg]
    · have hB_lt : deg (Polynomial.aeval u q * v) < (↑(2 * kk * kk) : WithBot ℕ) := by
        rw [hBdeg (hq := hqne)]
        have hB_le : 2 • q.degree + 3 ≤ (↑(2 * kk) : WithBot ℕ) := by
          rw [← hcoord]; exact le_max_right _ _
        rw [hBval_of_ne hqne] at hB_le
        have hle : 2 * q.natDegree + 3 ≤ 2 * kk := (WithBot.coe_le_coe (α := ℕ)).mp hB_le
        have hlt2 : 2 * q.natDegree + 3 < 2 * kk := by
          rcases lt_or_eq_of_le hle with h | h
          · exact h
          · exfalso; omega
        have hmul : kk * (2 * q.natDegree + 3) < kk * (2 * kk) :=
          Nat.mul_lt_mul_of_pos_left hlt2 hkkpos
        have hnat : kk * (2 * q.natDegree + 3) < 2 * kk * kk := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
        exact (WithBot.coe_lt_coe (α := ℕ) (a := kk * (2 * q.natDegree + 3))
          (b := 2 * kk * kk)).mpr hnat
      have hlt : deg (Polynomial.aeval u q * v) < deg (Polynomial.aeval u p) := by
        rw [hAdeg]; exact hB_lt
      have hd : deg (Polynomial.aeval u p + Polynomial.aeval u q * v) =
          (↑(2 * kk * kk) : WithBot ℕ) := by
        rw [add_comm, deg_add_eq_of_lt hlt, hAdeg]
      have hx2 : deg (Polynomial.aeval u p + Polynomial.aeval u q * v) = 2 := by
        rw [← hψu_eq, hψx, deg_xC]
      rw [hx2] at hd
      exact hd
  have hkk1 : kk = 1 := by
    have hnum : 2 * kk * kk = 2 := by
      exact (WithBot.coe_inj (α := ℕ) (a := 2 * kk * kk) (b := 2)).mp hkey.symm
    have hsq : kk * kk = 1 := by
      have h' : 2 * (kk * kk) = 2 * 1 := by
        calc 2 * (kk * kk) = 2 * kk * kk := by ring
          _ = 2 := hnum
          _ = 2 * 1 := by ring
      exact Nat.mul_left_cancel (by norm_num : 0 < 2) h'
    exact Nat.dvd_one.mp ⟨kk, hsq.symm⟩
  have hdu2 : deg u = (2 : WithBot ℕ) := by rw [hdu, hkk1]; norm_num
  have hdv3 : deg v = (3 : WithBot ℕ) := by rw [hdv, hkk1]; norm_num
  have hpk1 : p.natDegree = 1 := by rw [hpk, hkk1]
  have hcoord1 : max (2 • p.degree) (2 • q.degree + 3) = (2 : WithBot ℕ) := by
    rw [← deg_smul_basis_mk p q, hu_eq, hdu2]
  have hq0 : q = 0 := by
    by_contra hqne
    have hB_le : 2 • q.degree + 3 ≤ (2 : WithBot ℕ) := by
      rw [← hcoord1]
      exact le_max_right _ _
    rw [hBval_of_ne hqne] at hB_le
    have hle : 2 * q.natDegree + 3 ≤ 2 := (WithBot.coe_le_coe (α := ℕ)).mp hB_le
    omega
  have hu_aeval : u = Polynomial.aeval xC p := by
    rw [← hu_eq, hq0]
    simp [smul_one_eq_aeval]
  obtain ⟨a, b, hpab⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one (by rw [hpk1])
  have ha : a ≠ 0 := by
    intro ha0
    have hdeg : p.degree = (1 : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hpne, hpk1]; norm_num
    rw [hpab, ha0] at hdeg
    simp only [Polynomial.C_0, zero_mul, zero_add] at hdeg
    have hb : (Polynomial.C b).degree ≤ (0 : WithBot ℕ) := Polynomial.degree_C_le
    rw [hdeg] at hb
    exact absurd hb (by norm_num)
  obtain ⟨c, e, hv_eq⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq v
  have hcoordv : max (2 • c.degree) (2 • e.degree + 3) = (3 : WithBot ℕ) := by
    rw [← deg_smul_basis_mk c e, hv_eq, hdv3]
  have he_ne : e ≠ 0 := by
    intro he0
    have hB0 : 2 • e.degree + 3 = (⊥ : WithBot ℕ) := by
      rw [he0, Polynomial.degree_zero]
      simp
    rw [hB0, max_bot_right] at hcoordv
    rcases eq_or_ne c 0 with hc0 | hcne
    · rw [hc0, Polynomial.degree_zero, two_nsmul, WithBot.bot_add] at hcoordv
      exact (by simp : (⊥ : WithBot ℕ) ≠ (3 : WithBot ℕ)) hcoordv
    · rw [Polynomial.degree_eq_natDegree hcne, nsmul_coe] at hcoordv
      have h2 : 2 * c.natDegree = 3 := (WithBot.coe_inj (α := ℕ)).mp hcoordv
      omega
  have hedeg : e.natDegree = 0 := by
    have hB_le : 2 • e.degree + 3 ≤ (3 : WithBot ℕ) := by
      have h := le_max_right (2 • c.degree) (2 • e.degree + 3)
      rwa [hcoordv] at h
    rw [hBval_of_ne he_ne] at hB_le
    have hle : 2 * e.natDegree + 3 ≤ 3 := (WithBot.coe_le_coe (α := ℕ)).mp hB_le
    omega
  obtain ⟨e0, he0⟩ := Polynomial.natDegree_eq_zero.mp hedeg
  have he_eq : e = Polynomial.C e0 := he0.symm
  have hσu : signC u = u := by
    rw [hu_aeval]
    rw [← Polynomial.aeval_algHom_apply signC xC p, signC_xC]
  have signC_mkX : signC ((WeierstrassCurve.Affine.CoordinateRing.mk W)
      (Polynomial.X : Polynomial (Polynomial F))) = -yC := by
    simpa [yC] using signC_yC
  have hσv : signC v = c • (1 : Coord) - e • yC := by
    have h2 := signC_smul e ((WeierstrassCurve.Affine.CoordinateRing.mk W)
      (Polynomial.X : Polynomial (Polynomial F)))
    rw [← hv_eq, map_add, signC_smul c 1, h2, signC_mkX, map_one]
    rw [smul_neg, sub_eq_add_neg]
  have hσv_sq : (signC v) ^ 2 = u ^ 3 - u := by
    calc (signC v) ^ 2 = signC (v ^ 2) := by rw [map_pow]
      _ = signC (u ^ 3 - u) := by rw [hv_sq]
      _ = u ^ 3 - u := by rw [map_sub, map_pow, hσu]
  have hfac : (v - signC v) * (v + signC v) = 0 := by
    calc (v - signC v) * (v + signC v) = v ^ 2 - (signC v) ^ 2 := by ring
      _ = 0 := by rw [hv_sq, hσv_sq, sub_self]
  have hdiff : v - signC v = (2 * e) • yC := by
    rw [hσv, ← hv_eq]
    change c • (1 : Coord) + e • yC - (c • (1 : Coord) - e • yC) = (2 * e) • yC
    rw [show c • (1 : Coord) + e • yC - (c • (1 : Coord) - e • yC) = e • yC + e • yC by abel]
    rw [show (2 : Polynomial F) * e = e + e from two_mul e, add_smul]
  have hplus : v + signC v = (2 * c) • (1 : Coord) := by
    rw [hσv, ← hv_eq]
    change c • (1 : Coord) + e • yC + (c • (1 : Coord) - e • yC) = (2 * c) • (1 : Coord)
    rw [show c • (1 : Coord) + e • yC + (c • (1 : Coord) - e • yC) = c • (1 : Coord) + c • (1 : Coord) by abel]
    rw [show (2 : Polynomial F) * c = c + c from two_mul c, add_smul]
  rw [hdiff, hplus] at hfac
  have hprod : (2 * e) * (2 * c) = 0 := by
    have hfac' : ((2 * e) * (2 * c)) • yC = 0 := by
      have h := hfac
      rw [show ((2 * e) • yC) * ((2 * c) • (1 : Coord)) = ((2 * e) * (2 * c)) • yC from by
        calc ((2 * e) • yC) * ((2 * c) • (1 : Coord))
            = (2 * e) • (yC * ((2 * c) • (1 : Coord))) := by rw [smul_mul_assoc]
          _ = (2 * e) • ((2 * c) • (yC * 1)) := by rw [mul_smul_comm]
          _ = (2 * e) • ((2 * c) • yC) := by rw [mul_one]
          _ = ((2 * e) * (2 * c)) • yC := by rw [smul_smul]] at h
      exact h
    rw [Algebra.smul_def] at hfac'
    rcases mul_eq_zero.mp hfac' with h | h
    · exact algebraMap_injective (by simpa using h)
    · exact absurd h yC_ne_zero
  have h2poly : (2 : Polynomial F) ≠ 0 := by
    rw [show (2 : Polynomial F) = Polynomial.C (2 : F) from (Polynomial.C_eq_natCast 2).symm]
    exact Polynomial.C_ne_zero.mpr (by norm_num)
  have hc0 : c = 0 := by
    have h2e : (2 : Polynomial F) * e ≠ 0 := mul_ne_zero h2poly he_ne
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h h2e
    · rcases mul_eq_zero.mp h with h2c | hc
      · exact absurd h2c h2poly
      · exact hc
  have hv_simple : v = e0 • yC := by
    rw [← hv_eq, hc0, he_eq]
    rw [zero_smul, zero_add, Algebra.smul_def, Algebra.smul_def]
    rw [Polynomial.C_eq_algebraMap]
    rw [← IsScalarTower.algebraMap_apply F (Polynomial F) Coord e0]
    rfl
  have he0sq : e0 * e0 = 1 := by
    have h : (e0 * e0) • yC = (1 : F) • yC := by
      have hψ' := hψv
      rw [hv_simple, map_smul, ← hv, hv_simple, smul_smul] at hψ'
      rw [hψ', one_smul]
    have h' : algebraMap F Coord (e0 * e0) = algebraMap F Coord 1 := by
      apply mul_right_cancel₀ yC_ne_zero
      rw [← Algebra.smul_def, ← Algebra.smul_def, h]
    exact algebraMap_F_injective h'
  have hp_poly : (p ^ 3 - p : Polynomial F) =
      (Polynomial.X : Polynomial F) ^ 3 - Polynomial.X := by
    apply algebraMap_injective
    rw [← xC_aeval_eq_algebraMap, ← xC_aeval_eq_algebraMap]
    have hL : Polynomial.aeval xC (p ^ 3 - p) = u ^ 3 - u := by
      rw [map_sub, map_pow, ← hu_aeval]
    have hR : Polynomial.aeval xC ((Polynomial.X : Polynomial F) ^ 3 - Polynomial.X) = yC ^ 2 := by
      rw [map_sub, map_pow]
      simp [yC_sq]
    rw [hL, hR, ← hv_sq, hv_simple]
    calc (e0 • yC) ^ 2 = (e0 * e0) • (yC ^ 2) := by
          rw [Algebra.smul_def, Algebra.smul_def, map_mul]; ring
      _ = (1 : F) • (yC ^ 2) := by rw [he0sq]
      _ = yC ^ 2 := one_smul _ _
  have h_eval (t : F) : (a * t + b) ^ 3 - (a * t + b) = t ^ 3 - t := by
    have h := congrArg (fun q : Polynomial F => q.eval t) hp_poly
    rw [hpab] at h
    simpa [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X] using h
  have h0 := h_eval 0
  have h1 := h_eval 1
  have hm1 := h_eval (-1)
  have h2 := h_eval 2
  have hb0 : b = 0 := by
    by_contra hbne
    have hb2 : b ^ 2 = 1 := by
      have h : b * b ^ 2 = b * 1 := by linear_combination h0
      exact mul_left_cancel₀ hbne h
    have hA : a ^ 2 + 3 * b ^ 2 = 1 := by
      have h : 2 * a * (a ^ 2 + 3 * b ^ 2 - 1) = 0 := by
        linear_combination h1 - hm1
      have h2a : (2 : F) * a ≠ 0 := mul_ne_zero (by norm_num) ha
      have hfac : a ^ 2 + 3 * b ^ 2 - 1 = 0 := (mul_eq_zero.mp h).resolve_left h2a
      linear_combination hfac
    have hB : b ^ 2 + 3 * a ^ 2 = 1 := by
      have h : 2 * b * (b ^ 2 + 3 * a ^ 2 - 1) = 0 := by
        linear_combination h1 + hm1
      have h2b : (2 : F) * b ≠ 0 := mul_ne_zero (by norm_num) hbne
      have hfac : b ^ 2 + 3 * a ^ 2 - 1 = 0 := (mul_eq_zero.mp h).resolve_left h2b
      linear_combination hfac
    have hAB : a ^ 2 = b ^ 2 := by
      linear_combination (1 / 2 : F) * (hB - hA)
    have h4 : 4 * b ^ 2 = 1 := by
      rw [hAB] at hA
      linear_combination hA
    have h41 : (4 : F) = 1 := by
      calc (4 : F) = 4 * b ^ 2 := by rw [hb2]; ring
        _ = 1 := h4
    exact (by norm_num : (4 : F) ≠ 1) h41
  have ha3 : a ^ 3 = a := by
    have h1' := h1
    rw [hb0] at h1'
    simp only [add_zero] at h1'
    linear_combination h1'
  have ha1 : a = 1 := by
    have h2' := h2
    rw [hb0] at h2'
    simp only [add_zero] at h2'
    have : 6 * a = 6 * 1 := by linear_combination h2' - 8 * ha3
    exact mul_left_cancel₀ (by norm_num : (6 : F) ≠ 0) this
  have hpX : p = (Polynomial.X : Polynomial F) := by
    rw [hpab, hb0, ha1]
    simp
  have hu_x : u = xC := by
    rw [hu_aeval, hpX]
    simp
  have hv_sign : v = yC ∨ v = -yC := by
    rw [hv_simple]
    have hfac' : (e0 - 1) * (e0 + 1) = 0 := by
      calc (e0 - 1) * (e0 + 1) = e0 * e0 - 1 := by ring
        _ = 0 := by rw [he0sq, sub_self]
    rcases mul_eq_zero.mp hfac' with h | h
    · left
      have : e0 = 1 := by linear_combination h
      rw [this, one_smul]
    · right
      have : e0 = -1 := by linear_combination h
      rw [this, neg_smul, one_smul]
  constructor
  · exact hu.symm.trans hu_x
  · simpa [hv] using hv_sign

theorem S2482CoordinateRingInvolution_xR :
    S2482CoordinateRingInvolution xR = xR := by
  simp [S2482CoordinateRingInvolution, S2482AffineInvolutionAlgHom, xR]

theorem S2482CoordinateRingInvolution_yR :
    S2482CoordinateRingInvolution yR = -yR := by
  simp [S2482CoordinateRingInvolution, S2482AffineInvolutionAlgHom, yR, Ideal.Quotient.liftₐ]

theorem algHom_ext_gen {f g : S2482CoordinateRing →ₐ[F] S2482CoordinateRing}
    (hx : f xR = g xR) (hy : f yR = g yR) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simpa [xR] using hx
  · simpa [yR] using hy

/-- The order-two algebra automorphism classification for the S2482 coordinate ring. -/
theorem S2482OrderTwoAlgAutClassification :
    LeanFormal.IUT.XiFPaper.S2482QiNontrivialActual.S2482OrderTwoAlgAutClassification := by
  intro φ hφ
  have hφ' : ∀ y : S2482CoordinateRing, φ (φ y) = y := by
    intro y
    have h := congrArg (fun f : S2482CoordinateRing →ₐ[F] S2482CoordinateRing => f y) hφ
    simpa [AlgHom.comp_apply] using h
  let ψ : Coord ≃ₐ[F] Coord := (e.symm.trans φ).trans e
  have hψ : ψ.toAlgHom.comp ψ.toAlgHom = AlgHom.id F Coord := by
    apply AlgHom.ext
    intro z
    simp [ψ, hφ']
  obtain ⟨hψx, hψy⟩ := orderTwo_fixes ψ hψ
  have hx : e.symm xC = xR := by
    apply e.injective
    rw [AlgEquiv.apply_symm_apply, e_xR]
  have hy : e.symm yC = yR := by
    apply e.injective
    rw [AlgEquiv.apply_symm_apply, e_yR]
  have hφx : φ xR = xR := by
    apply e.injective
    have h := hψx
    change e (φ (e.symm xC)) = xC at h
    rw [hx] at h
    rwa [e_xR]
  have hφy : φ yR = yR ∨ φ yR = -yR := by
    rcases hψy with h | h
    · left
      apply e.injective
      have h' := h
      change e (φ (e.symm yC)) = yC at h'
      rw [hy] at h'
      rwa [e_yR]
    · right
      apply e.injective
      have h' := h
      change e (φ (e.symm yC)) = -yC at h'
      rw [hy] at h'
      rw [h', map_neg, e_yR]
  rcases hφy with hy' | hy'
  · left
    apply algHom_ext_gen
    · exact hφx
    · exact hy'
  · right
    apply algHom_ext_gen
    · rw [S2482CoordinateRingInvolution_xR]
      exact hφx
    · rw [S2482CoordinateRingInvolution_yR]
      exact hy'

#print axioms orderTwo_fixes
#print axioms S2482OrderTwoAlgAutClassification
#print axioms S2482CoordinateRingInvolution_yR

end LeanFormal.IUT.XiFPaper.S2482OrderTwoAlgAutClassificationActual
end