import tmp.sheaf.xif.paper.S2482QiNontrivialActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.LinearAlgebra.FreeModule.Norm

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482OrderTwoAlgAutClassificationAltActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2482QiNontrivialActual
open WeierstrassCurve.Affine
open Polynomial

abbrev Poly : Type := Polynomial F

abbrev Wc : WeierstrassCurve F := S2482Curve

abbrev Coord : Type := WeierstrassCurve.Affine.CoordinateRing Wc

abbrev polyWc : Polynomial Poly := WeierstrassCurve.Affine.polynomial Wc

abbrev xC : Coord := CoordinateRing.mk Wc (C (X : Poly))

abbrev yC : Coord := CoordinateRing.mk Wc (X : Polynomial Poly)

theorem Wc_polynomial_eq :
    polyWc = (X : Polynomial Poly) ^ 2 - C ((X : Poly) ^ 3 - X) := by
  simp only [polyWc, WeierstrassCurve.Affine.polynomial, Wc, S2482Curve]
  simp
  ring

theorem yC_sq : yC ^ 2 = xC ^ 3 - xC := by
  have h0 : AdjoinRoot.mk polyWc polyWc = 0 := AdjoinRoot.mk_self
  have hpoly : polyWc = (X : Polynomial Poly) ^ 2 - C ((X : Poly) ^ 3 - X) := Wc_polynomial_eq
  have h1 : AdjoinRoot.mk polyWc ((X : Polynomial Poly) ^ 2 - C ((X : Poly) ^ 3 - X)) = 0 := by
    rw [← hpoly]
    exact h0
  have hC : AdjoinRoot.mk polyWc (C ((X : Poly) ^ 3 - X)) = xC ^ 3 - xC := by
    simp only [map_sub, map_pow]
  have h' : yC ^ 2 - AdjoinRoot.mk polyWc (C ((X : Poly) ^ 3 - X)) = 0 := by
    simpa [yC, xC, CoordinateRing.mk, map_sub, map_pow] using h1
  rw [hC] at h'
  linear_combination h'

theorem xC_eq_algebraMap : xC = algebraMap Poly Coord (X : Poly) := rfl

theorem yC_eq_root : yC = AdjoinRoot.root polyWc := rfl

theorem algHom_ext_Coord {T : Type*} [CommSemiring T] [Algebra F T]
    {f g : Coord →ₐ[F] T} (hx : f xC = g xC) (hy : f yC = g yC) : f = g := by
  apply AdjoinRoot.algHom_ext' (p := polyWc) (S := F) (T := T)
  · apply Polynomial.algHom_ext
    simpa [xC, CoordinateRing.mk, AdjoinRoot.coe_ofAlgHom] using hx
  · simpa [yC, CoordinateRing.mk] using hy

abbrev xR : S2482CoordinateRing :=
  Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 0)

abbrev yR : S2482CoordinateRing :=
  Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 1)

theorem S2482AffinePolynomial_eq :
    S2482AffinePolynomial =
      MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 + MvPolynomial.X 0 := by
  simp only [S2482AffinePolynomial,
    LeanFormal.IUT.IUTII.Frobenioid.Example36.weierstrassAffinePolynomial, S2482Curve]
  simp
  ring

theorem yR_sq : yR ^ 2 = xR ^ 3 - xR := by
  have hmem : (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 + MvPolynomial.X 0) ∈
      Ideal.span {S2482AffinePolynomial} := by
    rw [← S2482AffinePolynomial_eq]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hzero : Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial})
      (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 + MvPolynomial.X 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have h : yR ^ 2 - xR ^ 3 + xR = 0 := by
    simpa [xR, yR, map_add, map_sub, map_pow] using hzero
  linear_combination h

theorem algHom_ext_R {T : Type*} [CommSemiring T] [Algebra F T]
    {f g : S2482CoordinateRing →ₐ[F] T} (hx : f xR = g xR) (hy : f yR = g yR) : f = g := by
  apply Ideal.Quotient.algHom_ext F
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simpa [xR] using hx
  · simpa [yR] using hy

noncomputable def toModel : S2482CoordinateRing →ₐ[F] Coord :=
  Ideal.Quotient.liftₐ (Ideal.span {S2482AffinePolynomial})
    (MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then xC else yC)) (by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨q, rfl⟩ := ha
      have hp : MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then xC else yC)
          S2482AffinePolynomial = 0 := by
        rw [S2482AffinePolynomial_eq]
        simp only [map_add, map_sub, map_pow]
        rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
        have h10 : (1 : Fin 2) ≠ 0 := by decide
        simp only [if_pos rfl, if_neg h10, if_true, if_false]
        linear_combination yC_sq
      rw [map_mul, hp, zero_mul])

theorem toModel_xR : toModel xR = xC := by
  simp [toModel, xR]

theorem toModel_yR : toModel yR = yC := by
  simp [toModel, yR]

noncomputable def fromModel : Coord →ₐ[F] S2482CoordinateRing :=
  AdjoinRoot.liftAlgHom polyWc (Polynomial.aeval xR) yR (by
    rw [Wc_polynomial_eq]
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, map_sub, map_pow]
    have hx : (↑(Polynomial.aeval (R := F) xR) : Poly →+* S2482CoordinateRing) (X : Poly) = xR := by
      simp
    rw [hx, yR_sq]
    ring)

theorem fromModel_xC : fromModel xC = xR := by
  rw [show xC = AdjoinRoot.of polyWc (X : Poly) from rfl]
  simp only [fromModel, AdjoinRoot.liftAlgHom_of]
  simp

theorem fromModel_yC : fromModel yC = yR := by
  rw [yC_eq_root]
  show AdjoinRoot.liftAlgHom polyWc (Polynomial.aeval (R := F) xR) yR _ (AdjoinRoot.root polyWc) = yR
  rw [AdjoinRoot.liftAlgHom_root]

theorem fromModel_comp_toModel :
    fromModel.comp toModel = AlgHom.id F S2482CoordinateRing := by
  apply algHom_ext_R
  · rw [AlgHom.comp_apply, toModel_xR, fromModel_xC, AlgHom.id_apply]
  · rw [AlgHom.comp_apply, toModel_yR, fromModel_yC, AlgHom.id_apply]

theorem toModel_comp_fromModel :
    toModel.comp fromModel = AlgHom.id F Coord := by
  apply algHom_ext_Coord
  · rw [AlgHom.comp_apply, fromModel_xC, toModel_xR, AlgHom.id_apply]
  · rw [AlgHom.comp_apply, fromModel_yC, toModel_yR, AlgHom.id_apply]

noncomputable def e : S2482CoordinateRing ≃ₐ[F] Coord :=
  AlgEquiv.ofAlgHom toModel fromModel toModel_comp_fromModel fromModel_comp_toModel

theorem e_xR : e xR = xC := toModel_xR

theorem e_yR : e yR = yC := toModel_yR

theorem e_symm_xC : e.symm xC = xR := by rw [← e_xR, AlgEquiv.symm_apply_apply]

theorem e_symm_yC : e.symm yC = yR := by rw [← e_yR, AlgEquiv.symm_apply_apply]

noncomputable def signC : Coord →ₐ[F] Coord :=
  AdjoinRoot.liftAlgHom polyWc (IsScalarTower.toAlgHom F Poly Coord) (-yC) (by
    rw [Wc_polynomial_eq]
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, map_sub, map_pow]
    have hx : (↑(IsScalarTower.toAlgHom F Poly Coord) : Poly →+* Coord) (X : Poly) = xC := rfl
    rw [neg_sq, yC_sq, hx]
    ring)

theorem signC_xC : signC xC = xC := by
  rw [show xC = AdjoinRoot.of polyWc (X : Poly) from rfl]
  simp only [signC, AdjoinRoot.liftAlgHom_of]
  exact xC_eq_algebraMap.symm

theorem signC_yC : signC yC = -yC := by
  rw [yC_eq_root]
  simp [signC, AdjoinRoot.liftAlgHom_root]

theorem signC_algebraMap (a : Poly) : signC (algebraMap Poly Coord a) = algebraMap Poly Coord a := by
  rw [show algebraMap Poly Coord a = AdjoinRoot.of polyWc a from rfl, signC,
    AdjoinRoot.liftAlgHom_of]
  rfl

theorem signC_mul_yC (z : Coord) : signC (z * yC) = signC z * (-yC) := by
  rw [map_mul, signC_yC]

theorem S2482CoordinateRingInvolution_xR : S2482CoordinateRingInvolution xR = xR := by
  simp [S2482CoordinateRingInvolution, S2482AffineInvolutionAlgHom,
    Ideal.Quotient.liftₐ, xR]

theorem S2482CoordinateRingInvolution_yR : S2482CoordinateRingInvolution yR = -yR := by
  simp [S2482CoordinateRingInvolution, S2482AffineInvolutionAlgHom,
    Ideal.Quotient.liftₐ, yR]



theorem algebraMap_Poly_Coord_inj : Function.Injective (algebraMap Poly Coord) := by
  intro a b hab
  have h0 : (a - b) • (1 : Coord) + (0 : Poly) • yC = 0 := by
    rw [zero_smul, add_zero, sub_smul, Algebra.smul_def, Algebra.smul_def, mul_one, mul_one, hab,
      sub_self]
  have h1 := (CoordinateRing.smul_basis_eq_zero (W' := Wc) h0).1
  exact sub_eq_zero.mp h1

theorem orderTwo_classification_Coord (ψ : Coord ≃ₐ[F] Coord)
    (hψ : ψ.toAlgHom.comp ψ.toAlgHom = AlgHom.id F Coord) :
    ψ = AlgEquiv.refl ∨ ψ.toAlgHom = signC := by
  have hψapply : ∀ z, ψ (ψ z) = z := fun z => AlgHom.congr_fun hψ z
  haveI hfree : Module.Free Poly Coord := (monic_polynomial (W := Wc)).free_adjoinRoot
  haveI hfin : Module.Finite Poly Coord := (monic_polynomial (W := Wc)).finite_adjoinRoot
  have hxC_ne : xC ≠ 0 := by
    intro h
    have h1 : (Polynomial.X : Poly) • (1 : Coord) + (0 : Poly) • yC = 0 := by
      rw [zero_smul, add_zero, Algebra.smul_def, mul_one]
      exact h
    exact Polynomial.X_ne_zero (CoordinateRing.smul_basis_eq_zero (W' := Wc) h1).1
  have hyC_ne : yC ≠ 0 := by
    intro h
    have h1 : (0 : Poly) • (1 : Coord) + (1 : Poly) • yC = 0 := by
      rw [zero_smul, zero_add, one_smul, h]
    exact one_ne_zero (CoordinateRing.smul_basis_eq_zero (W' := Wc) h1).2
  set X : Coord := ψ xC with hXdef
  set Y : Coord := ψ yC with hYdef
  have hX_ne : X ≠ 0 := by
    rw [hXdef]
    intro h
    exact hxC_ne (ψ.injective (by simpa using h))
  have hY_ne : Y ≠ 0 := by
    rw [hYdef]
    intro h
    exact hyC_ne (ψ.injective (by simpa using h))
  have hYsq : Y ^ 2 = X ^ 3 - X := by
    have h1 : ψ (yC ^ 2) = (ψ yC) ^ 2 := map_pow ψ yC 2
    have h2 : ψ (xC ^ 3 - xC) = (ψ xC) ^ 3 - ψ xC := by rw [map_sub, map_pow]
    rw [hYdef, hXdef, ← h1, ← h2, yC_sq]
  have hfinrank : Module.finrank Poly Coord = 2 := by
    rw [Module.finrank_eq_card_basis (CoordinateRing.basis Wc)]
    simp
  have hnorm_xC : Algebra.norm Poly xC = (Polynomial.X : Poly) ^ 2 := by
    rw [xC_eq_algebraMap, Algebra.norm_algebraMap, hfinrank]
  have hnorm_xC_nd : (Algebra.norm Poly xC).natDegree = 2 := by
    rw [hnorm_xC, Polynomial.natDegree_pow]
    simp
  have hquot_xC : Module.finrank F (Coord ⧸ Ideal.span {xC}) = 2 := by
    rw [finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis Wc) hxC_ne, hnorm_xC_nd]
  have hmapX : Ideal.map (ψ : Coord →+* Coord) (Ideal.span {xC}) = Ideal.span {X} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have hquot_X : Module.finrank F (Coord ⧸ Ideal.span {X}) = 2 := by
    have hq := (Ideal.quotientEquivAlg (Ideal.span {xC}) (Ideal.span {X}) ψ hmapX.symm).toLinearEquiv
    rw [← hq.finrank_eq, hquot_xC]
  have hnormX_nd : (Algebra.norm Poly X).natDegree = 2 := by
    rw [← finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis Wc) hX_ne]
    exact hquot_X
  have hnormX_ne : Algebra.norm Poly X ≠ 0 := Algebra.norm_ne_zero_iff.mpr hX_ne

  obtain ⟨p, q, hpq⟩ := CoordinateRing.exists_smul_basis_eq (W' := Wc) X
  have hmaxX : max (2 • p.degree) (2 • q.degree + 3) = ((2 : ℕ) : WithBot ℕ) := by
    have h := CoordinateRing.degree_norm_smul_basis (W' := Wc) p q
    rw [show (p • (1 : Coord) + q • (CoordinateRing.mk Wc) Polynomial.X) = X from hpq] at h
    have hdeg : ((Algebra.norm Poly X).degree) = ((2 : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hnormX_ne, hnormX_nd]
    rw [hdeg] at h
    exact h.symm
  have hq0 : q = 0 := by
    by_contra hq
    have hle : 2 • q.degree + 3 ≤ ((2 : ℕ) : WithBot ℕ) := by
      have h := le_max_right (2 • p.degree) (2 • q.degree + 3)
      rwa [hmaxX] at h
    have hb : (2 • q.degree + 3 : WithBot ℕ) = ((2 * q.natDegree + 3 : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hq, two_nsmul]
      push_cast
      ring
    rw [hb] at hle
    have hle' : 2 * q.natDegree + 3 ≤ 2 := WithBot.coe_le_coe.mp hle
    omega
  have hpdeg : 2 • p.degree = (2 : WithBot ℕ) := by
    simpa [hq0] using hmaxX
  have hp_ne : p ≠ 0 := by
    intro hp
    apply hX_ne
    rw [← hpq, hq0, hp]
    simp
  have hpnd : p.natDegree = 1 := by
    have hpd : p.degree = (p.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hp_ne
    have h2 : (2 • p.degree : WithBot ℕ) = ((2 * p.natDegree : ℕ) : WithBot ℕ) := by
      rw [hpd, two_nsmul]
      push_cast
      ring
    rw [h2] at hpdeg
    have hEq : 2 * p.natDegree = 2 := WithBot.coe_inj.mp hpdeg
    omega
  have hp_eq : p = C (p.coeff 1) * Polynomial.X + C (p.coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one hpnd.le
  have hα : p.coeff 1 ≠ 0 := by
    have hlead : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp_ne
    have hcl : p.leadingCoeff = p.coeff 1 := by
      rw [Polynomial.leadingCoeff, hpnd]
    rwa [hcl] at hlead
  have hp_alg : X = algebraMap Poly Coord p := by
    rw [← hpq, hq0, zero_smul, add_zero, Algebra.smul_def, mul_one]
  have hX3 : X ^ 3 - X = algebraMap Poly Coord (p ^ 3 - p) := by
    rw [hp_alg, map_sub, map_pow]
  have hnormX3 : Algebra.norm Poly (X ^ 3 - X) = (p ^ 3 - p) ^ 2 := by
    rw [hX3, Algebra.norm_algebraMap, hfinrank]
  have hnormY_sq : (Algebra.norm Poly Y) ^ 2 = Algebra.norm Poly (X ^ 3 - X) := by
    rw [pow_two, ← map_mul, ← pow_two, hYsq]
  have hp3nd : (p ^ 3 - p).natDegree = 3 := by
    have hp3 : (p ^ 3).natDegree = 3 := by
      rw [Polynomial.natDegree_pow, hpnd]
    have hlt : p.natDegree < (p ^ 3).natDegree := by rw [hp3, hpnd]; norm_num
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, hp3]
  have hnormY_nd : (Algebra.norm Poly Y).natDegree = 3 := by
    have h2 : (Algebra.norm Poly Y) ^ 2 = (p ^ 3 - p) ^ 2 := by
      rw [hnormY_sq, hnormX3]
    have hnd := congrArg Polynomial.natDegree h2
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_pow, hp3nd] at hnd
    omega
  have hnormY_ne : Algebra.norm Poly Y ≠ 0 := Algebra.norm_ne_zero_iff.mpr hY_ne

  obtain ⟨r, s, hrs⟩ := CoordinateRing.exists_smul_basis_eq (W' := Wc) Y
  have hmaxY : max (2 • r.degree) (2 • s.degree + 3) = ((3 : ℕ) : WithBot ℕ) := by
    have h := CoordinateRing.degree_norm_smul_basis (W' := Wc) r s
    rw [show (r • (1 : Coord) + s • (CoordinateRing.mk Wc) Polynomial.X) = Y from hrs] at h
    have hdeg : ((Algebra.norm Poly Y).degree) = ((3 : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hnormY_ne, hnormY_nd]
    rw [hdeg] at h
    exact h.symm
  have hs_ne : s ≠ 0 := by
    intro hs
    rw [hs] at hmaxY
    have h3 : (2 • (0 : Poly).degree + 3 : WithBot ℕ) = ⊥ := by simp
    rw [h3, max_bot_right] at hmaxY
    rcases eq_or_ne r 0 with hr | hr
    · rw [hr] at hmaxY; simp at hmaxY
    · rw [Polynomial.degree_eq_natDegree hr, two_nsmul] at hmaxY
      push_cast at hmaxY
      have hnat : r.natDegree + r.natDegree = 3 := WithBot.coe_inj.mp hmaxY
      omega
  have hs_le : 2 • s.degree + 3 ≤ ((3 : ℕ) : WithBot ℕ) := by
    have h := le_max_right (2 • r.degree) (2 • s.degree + 3)
    rwa [hmaxY] at h
  have hs_nd : s.natDegree = 0 := by
    have hsd : s.degree = ((s.natDegree : ℕ) : WithBot ℕ) := Polynomial.degree_eq_natDegree hs_ne
    have hb : (2 • ((s.natDegree : ℕ) : WithBot ℕ) + 3 : WithBot ℕ) =
        ((2 * s.natDegree + 3 : ℕ) : WithBot ℕ) := by
      rw [two_nsmul]
      push_cast
      ring
    rw [hsd, hb] at hs_le
    have hle : 2 * s.natDegree + 3 ≤ 3 := by exact_mod_cast hs_le
    omega
  obtain ⟨sg, hsg⟩ := Polynomial.natDegree_eq_zero.mp hs_nd
  have hsg_ne : sg ≠ 0 := by
    intro h
    apply hs_ne
    rw [← hsg, h, map_zero]
  have hs_eq : s = C sg := hsg.symm
  have hr_le : 2 • r.degree ≤ ((3 : ℕ) : WithBot ℕ) := by
    have h := le_max_left (2 • r.degree) (2 • s.degree + 3)
    rwa [hmaxY] at h
  have hrnd : r.natDegree ≤ 1 := by
    rcases eq_or_ne r 0 with hr | hr
    · simp [hr]
    · rw [Polynomial.degree_eq_natDegree hr, two_nsmul] at hr_le
      push_cast at hr_le
      have hnat : r.natDegree + r.natDegree ≤ 3 := WithBot.coe_le_coe.mp hr_le
      omega
  have hYrepr : Y = algebraMap Poly Coord r + algebraMap Poly Coord s * yC := by
    rw [← hrs, Algebra.smul_def, Algebra.smul_def, mul_one]
  have hsignY : signC Y = algebraMap Poly Coord r - algebraMap Poly Coord s * yC := by
    rw [hYrepr, map_add, map_mul, signC_algebraMap, signC_algebraMap, signC_yC]
    ring
  have hconj : signC (Y ^ 2) = Y ^ 2 := by
    rw [hYsq, hX3, signC_algebraMap, ← hX3, ← hYsq]
  have hY2eq : Y ^ 2 = (signC Y) ^ 2 := by
    rw [← hconj, map_pow]
  have hfac : (Y - signC Y) * (Y + signC Y) = 0 := by
    calc (Y - signC Y) * (Y + signC Y) = Y ^ 2 - (signC Y) ^ 2 := by ring
      _ = 0 := by rw [hY2eq, sub_self]

  haveI hF : FaithfulSMul F Coord := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply (algebraMap F Poly).injective
    apply algebraMap_Poly_Coord_inj
    rw [IsScalarTower.algebraMap_apply F Poly Coord,
      IsScalarTower.algebraMap_apply F Poly Coord] at h
    exact h
  haveI : CharZero Coord := Algebra.charZero_of_charZero (A := Coord) (R := F)
  have h2c : (2 : Coord) ≠ 0 := by norm_num
  have hr0 : r = 0 := by
    rcases mul_eq_zero.mp hfac with h | h
    · exfalso
      have h2 : Y - signC Y = (2 : Coord) * (algebraMap Poly Coord s * yC) := by
        rw [hsignY, hYrepr]; ring
      rw [h2] at h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h h2c
      · rcases mul_eq_zero.mp h with h | h
        · exact hs_ne (algebraMap_Poly_Coord_inj (by simpa using h))
        · exact hyC_ne h
    · have h2 : Y + signC Y = (2 : Coord) * algebraMap Poly Coord r := by
        rw [hsignY, hYrepr]; ring
      rw [h2] at h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h h2c
      · exact algebraMap_Poly_Coord_inj (by simpa using h)
  have hYγ : Y = sg • yC := by
    rw [hYrepr, hr0, map_zero, zero_add, hs_eq, Algebra.smul_def]
    congr 1
  have hY2' : Y ^ 2 = algebraMap Poly Coord (C (sg ^ 2) * ((Polynomial.X : Poly) ^ 3 - Polynomial.X)) := by
    rw [hYγ, smul_pow, yC_sq, xC_eq_algebraMap, Algebra.smul_def]
    rw [map_mul, map_sub, map_pow]
    rw [show algebraMap Poly Coord (C (sg ^ 2)) = algebraMap F Coord (sg ^ 2) from by
      rw [show C (sg ^ 2) = algebraMap F Poly (sg ^ 2) from rfl,
        ← IsScalarTower.algebraMap_apply F Poly Coord]]
    rw [show algebraMap Poly Coord ((Polynomial.X : Poly) ^ 3) =
        (algebraMap Poly Coord Polynomial.X) ^ 3 from map_pow (algebraMap Poly Coord) (Polynomial.X : Poly) 3]
    rw [show algebraMap F Coord (sg ^ 2) = (algebraMap F Coord sg) ^ 2 from
      map_pow (algebraMap F Coord) sg 2]
  have hpoly : C (sg ^ 2) * ((Polynomial.X : Poly) ^ 3 - Polynomial.X) = p ^ 3 - p := by
    have h : algebraMap Poly Coord (C (sg ^ 2) * ((Polynomial.X : Poly) ^ 3 - Polynomial.X)) =
        algebraMap Poly Coord (p ^ 3 - p) := by
      rw [← hY2', ← hX3]
      exact hYsq
    exact algebraMap_Poly_Coord_inj h
  let q : Poly := C (sg ^ 2) * ((Polynomial.X : Poly) ^ 3 - Polynomial.X) - (p ^ 3 - p)
  have hq : q = 0 := by
    dsimp [q]
    rw [hpoly, sub_self]
  have hq2val : q.derivative.derivative.eval 0 = -6 * (p.coeff 1) ^ 2 * (p.coeff 0) := by
    dsimp [q]
    rw [hp_eq]
    simp [Polynomial.derivative_pow, Polynomial.derivative_mul]
    ring
  have hq1val : q.derivative.eval 0 = -(sg ^ 2) + p.coeff 1 - 3 * (p.coeff 1) * (p.coeff 0) ^ 2 := by
    dsimp [q]
    rw [hp_eq]
    simp [Polynomial.derivative_pow, Polynomial.derivative_mul]
    ring
  have hq0val : q.eval 1 = -(((p.coeff 1) + (p.coeff 0)) ^ 3 - ((p.coeff 1) + (p.coeff 0))) := by
    dsimp [q]
    rw [hp_eq]
    simp
  have hq2 : -6 * (p.coeff 1) ^ 2 * (p.coeff 0) = 0 := by
    have h := hq2val
    rw [hq] at h
    simpa using h.symm
  have hq1 : -(sg ^ 2) + p.coeff 1 - 3 * (p.coeff 1) * (p.coeff 0) ^ 2 = 0 := by
    have h := hq1val
    rw [hq] at h
    simpa using h.symm
  have hq0 : -(((p.coeff 1) + (p.coeff 0)) ^ 3 - ((p.coeff 1) + (p.coeff 0))) = 0 := by
    have h := hq0val
    rw [hq] at h
    simpa using h.symm
  have hβ : p.coeff 0 = 0 := by
    have h : (-6 : F) * ((p.coeff 1) ^ 2 * (p.coeff 0)) = 0 := by
      linear_combination hq2
    rcases mul_eq_zero.mp h with h6 | h
    · exact absurd h6 (by norm_num)
    · exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hα)
  have hsg2_α : sg ^ 2 = p.coeff 1 := by
    have h := hq1
    rw [hβ] at h
    linear_combination -h
  have hα2 : (p.coeff 1) ^ 2 = 1 := by
    have h := hq0
    rw [hβ] at h
    have h' : (p.coeff 1) ^ 3 - p.coeff 1 = 0 := by linear_combination -h
    have hfac : (p.coeff 1) * ((p.coeff 1) ^ 2 - 1) = 0 := by linear_combination h'
    rcases mul_eq_zero.mp hfac with h0 | h0
    · exact absurd h0 hα
    · linear_combination h0
  have hsg2_one : sg ^ 2 = 1 := by
    have h1 : ψ Y = yC := by rw [hYdef]; exact hψapply yC
    have h2 : ψ Y = (sg ^ 2) • yC := by
      rw [hYγ, map_smul, ← hYdef, hYγ, smul_smul]
      simp only [sq]
    rw [h1] at h2
    have h3 : (sg ^ 2 - 1) • yC = 0 := by
      rw [sub_smul, one_smul, ← h2, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · linear_combination h
    · exact absurd h hyC_ne
  have hα1 : p.coeff 1 = 1 := by rw [← hsg2_α, hsg2_one]
  have hX_eq : X = xC := by
    rw [hp_alg, hp_eq, hβ, hα1]
    simp [xC_eq_algebraMap]
  have hsg_cases : sg = 1 ∨ sg = -1 := by
    have hfac : (sg - 1) * (sg + 1) = 0 := by
      linear_combination hsg2_one
    rcases mul_eq_zero.mp hfac with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases hsg_cases with hsg1 | hsgneg
  · left
    have hψid : ψ.toAlgHom = AlgHom.id F Coord := by
      apply algHom_ext_Coord
      · show ψ xC = xC
        rw [← hXdef, hX_eq]
      · show ψ yC = yC
        rw [← hYdef, hYγ, hsg1]
        simp
    exact AlgEquiv.ext (fun z => AlgHom.congr_fun hψid z)
  · right
    apply algHom_ext_Coord
    · show ψ xC = signC xC
      rw [signC_xC, ← hXdef, hX_eq]
    · show ψ yC = signC yC
      rw [signC_yC, ← hYdef, hYγ, hsgneg]
      simp


theorem S2482OrderTwoAlgAutClassification_actual :
    S2482OrderTwoAlgAutClassification := by
  intro φ hφ
  let ψ : Coord ≃ₐ[F] Coord := e.symm.trans (φ.trans e)
  have hψ_apply : ∀ z : S2482CoordinateRing, e (φ z) = ψ (e z) := by
    intro z
    dsimp [ψ]
    rw [e.symm_apply_apply]
  have hψ : ψ.toAlgHom.comp ψ.toAlgHom = AlgHom.id F Coord := by
    apply AlgHom.ext
    intro z
    have h1 : ψ z = e (φ (e.symm z)) := by
      have := hψ_apply (e.symm z)
      rwa [e.apply_symm_apply] at this
    calc ψ (ψ z) = ψ (e (φ (e.symm z))) := by rw [h1]
      _ = e (φ (φ (e.symm z))) := (hψ_apply (φ (e.symm z))).symm
      _ = e (e.symm z) := by
        congr 1
        simpa using AlgHom.congr_fun hφ (e.symm z)
      _ = z := e.apply_symm_apply z
  rcases orderTwo_classification_Coord ψ hψ with h | h
  · left
    apply algHom_ext_R
    · have hx := hψ_apply xR
      rw [h] at hx
      exact e.injective (by simpa using hx)
    · have hy := hψ_apply yR
      rw [h] at hy
      exact e.injective (by simpa using hy)
  · right
    apply algHom_ext_R
    · rw [S2482CoordinateRingInvolution_xR]
      have hxψ : ψ (e xR) = signC (e xR) := AlgHom.congr_fun h (e xR)
      have hx : e (φ xR) = e xR := by
        rw [hψ_apply xR, hxψ, e_xR, signC_xC]
      exact e.injective hx
    · rw [S2482CoordinateRingInvolution_yR]
      have hyψ : ψ (e yR) = signC (e yR) := AlgHom.congr_fun h (e yR)
      have hy : e (φ yR) = e (-yR) := by
        rw [hψ_apply yR, hyψ, e_yR, signC_yC, map_neg, e_yR]
      exact e.injective hy


#print axioms orderTwo_classification_Coord
#print axioms S2482OrderTwoAlgAutClassification_actual
#check @S2482OrderTwoAlgAutClassification_actual

end LeanFormal.IUT.XiFPaper.S2482OrderTwoAlgAutClassificationAltActual
end
