/- G1-A: r-side and y-side localization identification (x<->y swap).
   chartR = n x^(n-1), chartR2 = n y^(n-1); swapChart is the x<->y automorphism of Chart n;
   it induces Localization.Away chartR ~ Localization.Away chartR2 (next file).
   This file: basic evaluation lemmas + swapChart_chartR / swapChart_chartR2.
   No sorry/admit/axiom/PUnit/True/toy. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatChartSwapActual
import tmp.sheaf.xif.paper.Mzk1G1FermatSmoothLocalizeActual
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartLocalizeSwapActual
open Polynomial MvPolynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothLocalizeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartSwapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothIntegralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothAttemptActual

/-- y-side localization element: chartR2 = n y^(n-1). -/
noncomputable def chartR2 (n : Nat) : Chart n :=
  (n : Chart n) * chartY n ^ (n - 1)

/-- fermatCurvePoly is invariant under x<->y. -/
theorem swapA2_fermatCurvePoly (n : Nat) :
    swapA2 (fermatCurvePoly n) = fermatCurvePoly n := by
  simp only [fermatCurvePoly, swapA2, MvPolynomial.renameEquiv_apply, map_sub, map_add,
    map_pow, map_one, MvPolynomial.rename_X, swap2_zero, swap2_one]
  ring

theorem image_fermatCurvePoly_under_swap (n : Nat) :
    Set.image (swapA2 : MvPolynomial (Fin 2) ℚ → MvPolynomial (Fin 2) ℚ)
      ({fermatCurvePoly n} : Set (MvPolynomial (Fin 2) ℚ)) = {fermatCurvePoly n} := by
  ext x
  simp only [Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hy]
    exact swapA2_fermatCurvePoly n
  · intro hx
    exact ⟨fermatCurvePoly n, rfl, by rw [hx, swapA2_fermatCurvePoly]⟩

theorem map_fermatCurveIdeal (n : Nat) :
    (fermatCurveIdeal n).map (swapA2 : MvPolynomial (Fin 2) ℚ →+* MvPolynomial (Fin 2) ℚ)
      = fermatCurveIdeal n := by
  rw [fermatCurveIdeal, Ideal.map_span]
  change Ideal.span (Set.image (swapA2 : MvPolynomial (Fin 2) ℚ → MvPolynomial (Fin 2) ℚ)
    ({fermatCurvePoly n} : Set (MvPolynomial (Fin 2) ℚ))) = Ideal.span {fermatCurvePoly n}
  rw [image_fermatCurvePoly_under_swap]

/-- Chart ring x<->y automorphism. -/
noncomputable def swapChart (n : Nat) : Chart n ≃ₐ[ℚ] Chart n :=
  Ideal.quotientEquivAlg (fermatCurveIdeal n) (fermatCurveIdeal n) swapA2 (by
    show fermatCurveIdeal n
      = (fermatCurveIdeal n).map (swapA2 : MvPolynomial (Fin 2) ℚ →+* MvPolynomial (Fin 2) ℚ)
    rw [map_fermatCurveIdeal])

/-- Chart natCast = class of constant polynomial. -/
theorem natCast_eq_mk (n k : Nat) :
    (k : Chart n) = Ideal.Quotient.mk (fermatCurveIdeal n) (k : MvPolynomial (Fin 2) ℚ) := by
  have h1 : (k : Chart n) = algebraMap ℚ (Chart n) k :=
    (map_natCast (algebraMap ℚ (Chart n)) k).symm
  rw [h1, IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin 2) ℚ) (Chart n)]
  rw [Ideal.Quotient.algebraMap_eq]
  rw [show (algebraMap ℚ (MvPolynomial (Fin 2) ℚ) k) = (k : MvPolynomial (Fin 2) ℚ)
    from map_natCast _ k]

theorem chartR_eq_mk (n : Nat) :
    chartR n = Ideal.Quotient.mk (fermatCurveIdeal n)
      ((n : MvPolynomial (Fin 2) ℚ) * MvPolynomial.X 0 ^ (n - 1)) := by
  simp only [chartR, chartX, natCast_eq_mk]
  rw [← map_pow, ← map_mul]

theorem chartR2_eq_mk (n : Nat) :
    chartR2 n = Ideal.Quotient.mk (fermatCurveIdeal n)
      ((n : MvPolynomial (Fin 2) ℚ) * MvPolynomial.X 1 ^ (n - 1)) := by
  simp only [chartR2, chartY, natCast_eq_mk]
  rw [← map_pow, ← map_mul]

theorem swapA2_x_pow (n : Nat) :
    swapA2 ((n : MvPolynomial (Fin 2) ℚ) * MvPolynomial.X 0 ^ (n - 1))
      = (n : MvPolynomial (Fin 2) ℚ) * MvPolynomial.X 1 ^ (n - 1) := by
  rw [map_mul, map_pow, swapA2, MvPolynomial.renameEquiv_apply]
  simp [MvPolynomial.rename_X, swap2_zero, swap2_one]

theorem swapA2_y_pow (n : Nat) :
    swapA2 ((n : MvPolynomial (Fin 2) ℚ) * MvPolynomial.X 1 ^ (n - 1))
      = (n : MvPolynomial (Fin 2) ℚ) * MvPolynomial.X 0 ^ (n - 1) := by
  rw [map_mul, map_pow, swapA2, MvPolynomial.renameEquiv_apply]
  simp [MvPolynomial.rename_X, swap2_zero, swap2_one]

theorem swapChart_mk (n : Nat) (p : MvPolynomial (Fin 2) ℚ) :
    swapChart n (Ideal.Quotient.mk (fermatCurveIdeal n) p)
      = Ideal.Quotient.mk (fermatCurveIdeal n) (swapA2 p) := by
  unfold swapChart
  exact Ideal.quotientEquivAlg_mk _ _ _ p

theorem swapChart_chartR (n : Nat) : swapChart n (chartR n) = chartR2 n := by
  rw [chartR_eq_mk, swapChart_mk, swapA2_x_pow, ← chartR2_eq_mk]

theorem swapChart_chartR2 (n : Nat) : swapChart n (chartR2 n) = chartR n := by
  rw [chartR2_eq_mk, swapChart_mk, swapA2_y_pow, ← chartR_eq_mk]

#print axioms swapA2_fermatCurvePoly
#print axioms map_fermatCurveIdeal
#print axioms swapChart_mk
#print axioms swapChart_chartR
#print axioms swapChart_chartR2
theorem swapChart_toRingHom_chartR (n : Nat) :
    (swapChart n).toRingEquiv.toRingHom (chartR n) = chartR2 n := swapChart_chartR n

theorem swapChart_symm_toRingHom_chartR2 (n : Nat) :
    (swapChart n).symm.toRingEquiv.toRingHom (chartR2 n) = chartR n := by
  have h : (swapChart n).symm (chartR2 n) = chartR n := by
    apply_fun (swapChart n)
    rw [AlgEquiv.apply_symm_apply, swapChart_chartR]
  exact h

/-- r-侧局部化到 y-侧局部化的环同态（swapChart 诱导）。 -/
noncomputable def localizeSwapHom (n : Nat) :
    Localization.Away (chartR n) →+* Localization.Away (chartR2 n) :=
  IsLocalization.Away.lift (chartR n)
    (g := (algebraMap (Chart n) (Localization.Away (chartR2 n))).comp
      (swapChart n).toRingHom) (by
      rw [RingHom.comp_apply, swapChart_toRingHom_chartR]
      exact IsLocalization.Away.algebraMap_isUnit (chartR2 n))

/-- y-侧局部化到 r-侧局部化的环同态（逆方向）。 -/
noncomputable def localizeSwapHom2 (n : Nat) :
    Localization.Away (chartR2 n) →+* Localization.Away (chartR n) :=
  IsLocalization.Away.lift (chartR2 n)
    (g := (algebraMap (Chart n) (Localization.Away (chartR n))).comp
      (swapChart n).symm.toRingHom) (by
      rw [RingHom.comp_apply, swapChart_symm_toRingHom_chartR2]
      exact IsLocalization.Away.algebraMap_isUnit (chartR n))

theorem swapChart_toRingHom_apply_symm (n : Nat) (a : Chart n) :
    (swapChart n).toRingEquiv.toRingHom ((swapChart n).symm.toRingEquiv.toRingHom a) = a := by
  change (swapChart n) ((swapChart n).symm a) = a
  rw [AlgEquiv.apply_symm_apply]

theorem swapChart_symm_toRingHom_apply (n : Nat) (a : Chart n) :
    (swapChart n).symm.toRingEquiv.toRingHom ((swapChart n).toRingEquiv.toRingHom a) = a := by
  change (swapChart n).symm ((swapChart n) a) = a
  rw [AlgEquiv.symm_apply_apply]

theorem localizeSwapHom_comp (n : Nat) :
    (localizeSwapHom n).comp (localizeSwapHom2 n)
      = RingHom.id (Localization.Away (chartR2 n)) := by
  apply IsLocalization.ringHom_ext (M := Submonoid.powers (chartR2 n))
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply, RingHom.id_apply, localizeSwapHom, localizeSwapHom2,
    IsLocalization.Away.lift_eq]
  congr 1
  exact swapChart_toRingHom_apply_symm n a

theorem localizeSwapHom2_comp (n : Nat) :
    (localizeSwapHom2 n).comp (localizeSwapHom n)
      = RingHom.id (Localization.Away (chartR n)) := by
  apply IsLocalization.ringHom_ext (M := Submonoid.powers (chartR n))
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply, RingHom.id_apply, localizeSwapHom, localizeSwapHom2,
    IsLocalization.Away.lift_eq]
  congr 1
  exact swapChart_symm_toRingHom_apply n a

#print axioms localizeSwapHom
#print axioms localizeSwapHom_comp
#print axioms localizeSwapHom2_comp
/-- **r-侧与 y-侧局部化的 ℚ-代数同构**（swapChart 诱导）。 -/
noncomputable def localizeSwapEquiv (n : Nat) :
    Localization.Away (chartR n) ≃ₐ[ℚ] Localization.Away (chartR2 n) where
  toFun := localizeSwapHom n
  invFun := localizeSwapHom2 n
  left_inv s := by
    have h := RingHom.congr_fun (localizeSwapHom2_comp n) s
    simpa using h
  right_inv s := by
    have h := RingHom.congr_fun (localizeSwapHom_comp n) s
    simpa using h
  map_add' := map_add _
  map_mul' := map_mul _
  commutes' q := by
    rw [IsScalarTower.algebraMap_apply ℚ (Chart n) (Localization.Away (chartR n))]
    change localizeSwapHom n ((algebraMap (Chart n) (Localization.Away (chartR n)))
      (algebraMap ℚ (Chart n) q)) = algebraMap ℚ (Localization.Away (chartR2 n)) q
    rw [localizeSwapHom, IsLocalization.Away.lift_eq]
    rw [RingHom.comp_apply]
    change (algebraMap (Chart n) (Localization.Away (chartR2 n)))
      ((swapChart n : Chart n → Chart n) (algebraMap ℚ (Chart n) q))
      = algebraMap ℚ (Localization.Away (chartR2 n)) q
    rw [show (swapChart n : Chart n → Chart n) (algebraMap ℚ (Chart n) q)
        = algebraMap ℚ (Chart n) q from AlgEquiv.commutes (swapChart n) q]
    rw [IsScalarTower.algebraMap_apply ℚ (Chart n) (Localization.Away (chartR2 n))]

/-- **r-侧局部化 (R n)[1/r] 是 relative dim 1 standard smooth**（沿 localizeEquiv 从局部模型运输）。 -/
theorem loc_chartR_isStandardSmooth (n : Nat) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ (Localization.Away (chartR n)) := by
  haveI := fermatModel_isStandardSmooth n
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (1) (localizeEquiv n)

/-- **y-侧局部化 (R n)[1/r2] 是 relative dim 1 standard smooth**（x↔y 对称性 + 局部化运输）。 -/
theorem loc_chartR2_isStandardSmooth (n : Nat) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ (Localization.Away (chartR2 n)) := by
  haveI := modelSwap_isStandardSmooth n
  have e : ModelSwap n ≃ₐ[ℚ] Localization.Away (chartR2 n) :=
    ((ModelSwapEquiv n).symm).trans ((localizeEquiv n).trans (localizeSwapEquiv n))
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (1) e

#print axioms localizeSwapEquiv
#print axioms loc_chartR_isStandardSmooth
#print axioms loc_chartR2_isStandardSmooth



end LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartLocalizeSwapActual