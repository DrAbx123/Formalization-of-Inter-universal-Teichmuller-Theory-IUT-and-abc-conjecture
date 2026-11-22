/-
S2856: the two overlap ring lemmas hY and hZ for the chart-Y directed cover.

These are the two ring-level inputs for the gluing of the chart-negation morphism
across the two-chart overlap:
* hY: the chart-Y negation map, re-read in Away(1 + t1), inverts the
  chart-Y negation g0Ring;
* hZ: the chart-Z coordinates of the chart-Y map g1Ring agree with
  alpha composed with the chart-Z negation automorphism.
-/
import tmp.sheaf.xif.paper.S2855ChartYDirectedCoverActual
import tmp.sheaf.xif.paper.S2853E37NegationAutomorphismActual
import Mathlib.Tactic

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2853ChartYNegationActual
open LeanFormal.IUT.XiFPaper.S2855ChartYDirectedCoverActual
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2856HfYZRingActual


/-! ## 1. The comparison ring A2 = Away(1 + t1) and the base ring map -/

/-- The second overlap ring: localize the chart-Y overlap ring at 1 + t1. -/
noncomputable abbrev A2 (K : Type) [Field K] : Type :=
  Localization.Away (1 + t1 K)

/-- The base ring map R1 to A2, through the chart-Y overlap ring. -/
noncomputable abbrev baseRing (K : Type) [Field K] : R1 K →+* A2 K :=
  (algebraMap (A1 K) (A2 K)).comp (algebraMap (R1 K) (A1 K))

/-- The image of 1 + t1 in A2; it is a unit. -/
noncomputable abbrev c (K : Type) [Field K] : A2 K :=
  algebraMap (A1 K) (A2 K) (1 + t1 K)

/-- The unit 1 + t1 in A2. -/
noncomputable def cUnit (K : Type) [Field K] : (A2 K)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (x := 1 + t1 K) (S := A2 K)).unit

theorem cUnit_val (K : Type) [Field K] : (↑(cUnit K) : A2 K) = c K :=
  IsUnit.unit_spec _

theorem baseRing_one_add_tbar (K : Type) [Field K] :
    baseRing K (1 + tbar K) = c K := by
  have h1 : (algebraMap (R1 K) (A1 K)) (1 + tbar K) = 1 + t1 K := by
    rw [map_add, map_one, t1_eq_algebraMap]
  show (algebraMap (A1 K) (A2 K)) ((algebraMap (R1 K) (A1 K)) (1 + tbar K)) = c K
  rw [h1]

theorem baseRing_isUnit (K : Type) [Field K] :
    IsUnit (baseRing K (1 + tbar K)) := by
  rw [baseRing_one_add_tbar]
  exact ⟨cUnit K, cUnit_val K⟩

/-- The natural map from the chart-Y negation localization to A2. -/
noncomputable def base (K : Type) [Field K] :
    S2853ChartYNegRing K →+* A2 K :=
  Localization.awayLift (baseRing K) (1 + tbar K) (baseRing_isUnit K)

theorem base_algebraMap (K : Type) [Field K] (a : R1 K) :
    base K (algebraMap (R1 K) (S2853ChartYNegRing K) a) = baseRing K a := by
  change (Localization.awayLift (baseRing K) (1 + tbar K) (baseRing_isUnit K))
      ((algebraMap (R1 K) (Localization.Away (1 + tbar K))) a) = baseRing K a
  exact IsLocalization.Away.lift_eq (1 + tbar K) (baseRing_isUnit K) a

theorem base_unit (K : Type) [Field K] :
    base K (↑(S2853ChartYNegUnit K)) = c K := by
  have h1 : (↑(S2853ChartYNegUnit K) : S2853ChartYNegRing K) =
      algebraMap (R1 K) (S2853ChartYNegRing K) (1 + tbar K) :=
    IsUnit.unit_spec _
  rw [h1, base_algebraMap]
  exact baseRing_one_add_tbar K

theorem base_unit_inv (K : Type) [Field K] :
    base K (↑((S2853ChartYNegUnit K)⁻¹)) = ↑((cUnit K)⁻¹) := by
  have hmap : Units.map (base K).toMonoidHom (S2853ChartYNegUnit K) = cUnit K := by
    ext
    rw [Units.coe_map]
    change base K (↑(S2853ChartYNegUnit K)) = ↑(cUnit K)
    rw [base_unit K, cUnit_val K]
  have hinv : Units.map (base K).toMonoidHom ((S2853ChartYNegUnit K)⁻¹) = (cUnit K)⁻¹ := by
    rw [MonoidHom.map_inv, hmap]
  have h := congrArg (fun u : (A2 K)ˣ => (↑u : A2 K)) hinv
  rw [Units.coe_map] at h
  change base K (↑((S2853ChartYNegUnit K)⁻¹)) = ↑((cUnit K)⁻¹) at h
  exact h

/-! ## 2. The ring map uY : R1 to A2 and the induced phiY -/

/-- The ring map uY used to build phiY: on coordinates it is the chart-Y
negation formula read in A2. -/
noncomputable def uY (K : Type) [Field K] : R1 K →+* A2 K :=
  (base K).comp (g0Ring K)

theorem g0Ring_sbar (K : Type) [Field K] :
    g0Ring K (sbar K) = S2853ChartYNegS K := by
  simpa [g0Ring, g0Poly, sbar] using (S2853_hX0 K)

theorem g0Ring_tbar (K : Type) [Field K] :
    g0Ring K (tbar K) = S2853ChartYNegT K := by
  simpa [g0Ring, g0Poly, tbar] using (S2853_hX1 K)

theorem uY_sbar (K : Type) [Field K] :
    uY K (sbar K) = -(baseRing K (sbar K) * ↑((cUnit K)⁻¹)) := by
  calc uY K (sbar K)
      = base K (g0Ring K (sbar K)) := rfl
    _ = base K (S2853ChartYNegS K) := by rw [g0Ring_sbar]
    _ = base K (algebraMap (R1 K) (S2853ChartYNegRing K) (-(S2853ChartYS K)) *
          ↑((S2853ChartYNegUnit K)⁻¹)) := rfl
    _ = base K (algebraMap (R1 K) (S2853ChartYNegRing K) (-(S2853ChartYS K))) *
          base K (↑((S2853ChartYNegUnit K)⁻¹)) := map_mul _ _ _
    _ = baseRing K (-(S2853ChartYS K)) * ↑((cUnit K)⁻¹) := by
        rw [base_algebraMap, base_unit_inv]
    _ = -(baseRing K (sbar K) * ↑((cUnit K)⁻¹)) := by
        rw [map_neg, show S2853ChartYS K = sbar K from rfl]
        ring

theorem uY_tbar (K : Type) [Field K] :
    uY K (tbar K) = -(baseRing K (tbar K) * ↑((cUnit K)⁻¹)) := by
  calc uY K (tbar K)
      = base K (g0Ring K (tbar K)) := rfl
    _ = base K (S2853ChartYNegT K) := by rw [g0Ring_tbar]
    _ = base K (algebraMap (R1 K) (S2853ChartYNegRing K) (-(S2853ChartYT K)) *
          ↑((S2853ChartYNegUnit K)⁻¹)) := rfl
    _ = base K (algebraMap (R1 K) (S2853ChartYNegRing K) (-(S2853ChartYT K))) *
          base K (↑((S2853ChartYNegUnit K)⁻¹)) := map_mul _ _ _
    _ = baseRing K (-(S2853ChartYT K)) * ↑((cUnit K)⁻¹) := by
        rw [base_algebraMap, base_unit_inv]
    _ = -(baseRing K (tbar K) * ↑((cUnit K)⁻¹)) := by
        rw [map_neg, show S2853ChartYT K = tbar K from rfl]
        ring

theorem uY_one_add_tbar (K : Type) [Field K] :
    uY K (1 + tbar K) = ↑((cUnit K)⁻¹) := by
  have ht : baseRing K (tbar K) = algebraMap (A1 K) (A2 K) (t1 K) := by
    show (algebraMap (A1 K) (A2 K)) ((algebraMap (R1 K) (A1 K)) (tbar K)) =
      (algebraMap (A1 K) (A2 K)) (t1 K)
    congr 1
  have hc : (↑(cUnit K) : A2 K) = 1 + algebraMap (A1 K) (A2 K) (t1 K) := by
    rw [cUnit_val]
    show (algebraMap (A1 K) (A2 K)) (1 + t1 K) =
      1 + (algebraMap (A1 K) (A2 K)) (t1 K)
    rw [map_add, map_one]
  have hu : (↑((cUnit K)⁻¹) : A2 K) * ↑(cUnit K) = 1 := Units.inv_mul _
  have hstep : (1 - algebraMap (A1 K) (A2 K) (t1 K) * ↑((cUnit K)⁻¹)) *
      ↑(cUnit K) = 1 := by
    calc (1 - algebraMap (A1 K) (A2 K) (t1 K) * ↑((cUnit K)⁻¹)) * ↑(cUnit K)
        = ↑(cUnit K) - algebraMap (A1 K) (A2 K) (t1 K) *
            (↑((cUnit K)⁻¹) * ↑(cUnit K)) := by ring
      _ = ↑(cUnit K) - algebraMap (A1 K) (A2 K) (t1 K) * 1 := by rw [hu]
      _ = 1 := by rw [hc]; ring
  have hcancel : 1 - algebraMap (A1 K) (A2 K) (t1 K) * ↑((cUnit K)⁻¹) =
      ↑((cUnit K)⁻¹) :=
    (IsUnit.mul_left_inj (show IsUnit (↑(cUnit K) : A2 K) from ⟨cUnit K, rfl⟩)).mp (by
      rw [hstep, hu])
  rw [map_add, map_one, uY_tbar, ht]
  calc (1 : A2 K) + (-(algebraMap (A1 K) (A2 K) (t1 K) * ↑((cUnit K)⁻¹)))
      = 1 - algebraMap (A1 K) (A2 K) (t1 K) * ↑((cUnit K)⁻¹) := by ring
    _ = ↑((cUnit K)⁻¹) := hcancel

theorem uY_one_add_tbar_isUnit (K : Type) [Field K] :
    IsUnit (uY K (1 + tbar K)) := by
  rw [uY_one_add_tbar]
  exact (cUnit K)⁻¹.isUnit

/-- The inverse chart-Y negation map, from Away(1 + t) to Away(1 + t1). -/
noncomputable def φY (K : Type) [Field K] :
    S2853ChartYNegRing K →+* A2 K :=
  Localization.awayLift (uY K) (1 + tbar K) (uY_one_add_tbar_isUnit K)

theorem phiY_algebraMap (K : Type) [Field K] (a : R1 K) :
    φY K (algebraMap (R1 K) (S2853ChartYNegRing K) a) = uY K a := by
  change (Localization.awayLift (uY K) (1 + tbar K) (uY_one_add_tbar_isUnit K))
      ((algebraMap (R1 K) (Localization.Away (1 + tbar K))) a) = uY K a
  exact IsLocalization.Away.lift_eq (1 + tbar K) (uY_one_add_tbar_isUnit K) a

theorem phiY_unit (K : Type) [Field K] :
    φY K (↑(S2853ChartYNegUnit K)) = ↑((cUnit K)⁻¹) := by
  have h1 : (↑(S2853ChartYNegUnit K) : S2853ChartYNegRing K) =
      algebraMap (R1 K) (S2853ChartYNegRing K) (1 + tbar K) :=
    IsUnit.unit_spec _
  rw [h1, phiY_algebraMap]
  exact uY_one_add_tbar K

theorem phiY_unit_inv (K : Type) [Field K] :
    φY K (↑((S2853ChartYNegUnit K)⁻¹)) = ↑(cUnit K) := by
  have hmap : Units.map (φY K).toMonoidHom (S2853ChartYNegUnit K) = (cUnit K)⁻¹ := by
    ext
    rw [Units.coe_map]
    change φY K (↑(S2853ChartYNegUnit K)) = ↑((cUnit K)⁻¹)
    exact phiY_unit K
  have hinv : Units.map (φY K).toMonoidHom ((S2853ChartYNegUnit K)⁻¹) = ((cUnit K)⁻¹)⁻¹ := by
    rw [MonoidHom.map_inv, hmap]
  have h := congrArg (fun u : (A2 K)ˣ => (↑u : A2 K)) hinv
  rw [Units.coe_map] at h
  change φY K (↑((S2853ChartYNegUnit K)⁻¹)) = ↑(((cUnit K)⁻¹)⁻¹) at h
  rw [inv_inv] at h
  exact h

theorem phiY_negS (K : Type) [Field K] :
    φY K (S2853ChartYNegS K) = baseRing K (sbar K) := by
  have hS : S2853ChartYNegS K =
      algebraMap (R1 K) (S2853ChartYNegRing K) (-(S2853ChartYS K)) *
        ↑((S2853ChartYNegUnit K)⁻¹) := rfl
  rw [hS, map_mul, phiY_algebraMap, phiY_unit_inv]
  rw [show -(S2853ChartYS K) = -(sbar K) from rfl, map_neg, uY_sbar]
  have hu : (↑((cUnit K)⁻¹) : A2 K) * ↑(cUnit K) = 1 := Units.inv_mul _
  calc -(-(baseRing K (sbar K) * ↑((cUnit K)⁻¹))) * ↑(cUnit K)
      = (baseRing K (sbar K) * ↑((cUnit K)⁻¹)) * ↑(cUnit K) := by ring
    _ = baseRing K (sbar K) * (↑((cUnit K)⁻¹) * ↑(cUnit K)) := by ring
    _ = baseRing K (sbar K) * 1 := by rw [hu]
    _ = baseRing K (sbar K) := mul_one _

theorem phiY_negT (K : Type) [Field K] :
    φY K (S2853ChartYNegT K) = baseRing K (tbar K) := by
  have hT : S2853ChartYNegT K =
      algebraMap (R1 K) (S2853ChartYNegRing K) (-(S2853ChartYT K)) *
        ↑((S2853ChartYNegUnit K)⁻¹) := rfl
  rw [hT, map_mul, phiY_algebraMap, phiY_unit_inv]
  rw [show -(S2853ChartYT K) = -(tbar K) from rfl, map_neg, uY_tbar]
  have hu : (↑((cUnit K)⁻¹) : A2 K) * ↑(cUnit K) = 1 := Units.inv_mul _
  calc -(-(baseRing K (tbar K) * ↑((cUnit K)⁻¹))) * ↑(cUnit K)
      = (baseRing K (tbar K) * ↑((cUnit K)⁻¹)) * ↑(cUnit K) := by ring
    _ = baseRing K (tbar K) * (↑((cUnit K)⁻¹) * ↑(cUnit K)) := by ring
    _ = baseRing K (tbar K) * 1 := by rw [hu]
    _ = baseRing K (tbar K) := mul_one _

/-! ## 3. The first ring lemma hY -/

theorem hY (K : Type) [Field K] :
    (φY K).comp (g0Ring K) =
      (algebraMap (A1 K) (A2 K)).comp (algebraMap (R1 K) (A1 K)) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply]
    rw [show Ideal.Quotient.mk (E37ChartYIdeal K) (MvPolynomial.C a) = algebraMap K (R1 K) a from
      Ideal.Quotient.mk_algebraMap K (I := E37ChartYIdeal K) a]
    have hg : g0Ring K (algebraMap K (R1 K) a) = algebraMap K (S2853ChartYNegRing K) a := by
      rw [← Ideal.Quotient.mk_algebraMap K (I := E37ChartYIdeal K) a]
      simp [g0Ring, g0Poly, S2853G0Poly, MvPolynomial.eval₂Hom_C]
    rw [hg, IsScalarTower.algebraMap_apply K (R1 K) (S2853ChartYNegRing K),
      phiY_algebraMap]
    show base K (g0Ring K (algebraMap K (R1 K) a)) = baseRing K (algebraMap K (R1 K) a)
    rw [hg, IsScalarTower.algebraMap_apply K (R1 K) (S2853ChartYNegRing K), base_algebraMap]
  · intro i
    fin_cases i
    · simp only [RingHom.comp_apply]
      change (φY K) (g0Ring K (sbar K)) = baseRing K (sbar K)
      rw [show g0Ring K (sbar K) = S2853ChartYNegS K from g0Ring_sbar K, phiY_negS]
    · simp only [RingHom.comp_apply]
      change (φY K) (g0Ring K (tbar K)) = baseRing K (tbar K)
      rw [show g0Ring K (tbar K) = S2853ChartYNegT K from g0Ring_tbar K, phiY_negT]

/-! ## 4. The chart-Z side: g1Ring and the chart-Z negation -/

/-- The projection-side comparison map phiZ. -/
noncomputable abbrev φZ (K : Type) [Field K] : A1 K →+* A2 K :=
  algebraMap (A1 K) (A2 K)

theorem g1Unit_val (K : Type) [Field K] :
    (↑(g1Unit K) : Localization.Away (tY K)) = t1 K := by
  have h1 : (↑(g1Unit K) : Localization.Away (tY K)) =
      algebraMap (E37ChartYRing K) (Localization.Away (tY K)) (tY K) :=
    IsUnit.unit_spec _
  rw [h1, ← t1_eq_algebraMap]

theorem g1Unit_inv_val (K : Type) [Field K] :
    (↑((g1Unit K)⁻¹) : Localization.Away (tY K)) = tInv K := by
  let w : (Localization.Away (tY K))ˣ := ⟨t1 K, tInv K, t1_mul_tInv K, tInv_mul_t1 K⟩
  have hw : w = g1Unit K := by
    ext
    show t1 K = (↑(g1Unit K) : Localization.Away (tY K))
    rw [g1Unit_val]
  rw [← hw]
  rfl

theorem g1Ring_X (K : Type) [Field K] :
    g1Ring K (S2801E37X K) = s1 K * tInv K := by
  have h : g1Ring K (S2801E37X K) =
      algebraMap (E37ChartYRing K) (Localization.Away (tY K)) (S2853ChartYS K) *
        ↑((g1Unit K)⁻¹) := by
    show (Ideal.Quotient.lift (S2801E37Ideal K) (g1Poly K) _)
      (Ideal.Quotient.mk (S2801E37Ideal K) (MvPolynomial.X 0)) = _
    rw [Ideal.Quotient.lift_mk]
    simp [g1Poly, g1Vals]
  rw [h, g1Unit_inv_val, ← s1_eq_algebraMap]

theorem g1Ring_Y (K : Type) [Field K] :
    g1Ring K (S2801E37Y K) = -1 - tInv K := by
  have h : g1Ring K (S2801E37Y K) = -1 - ↑((g1Unit K)⁻¹) := by
    show (Ideal.Quotient.lift (S2801E37Ideal K) (g1Poly K) _)
      (Ideal.Quotient.mk (S2801E37Ideal K) (MvPolynomial.X 1)) = _
    rw [Ideal.Quotient.lift_mk]
    simp [g1Poly, g1Vals]
  rw [h, g1Unit_inv_val]

theorem alpha_X (K : Type) [Field K] :
    alpha K (S2801E37X K) = s1 K * tInv K := by
  simp [alpha, alphaPoly, evalVals, S2801E37X]

theorem chartZ_X (K : Type) [Field K] [DecidableEq K] :
    S2853RingHom K (S2801E37X K) = S2801E37X K := by
  simp [S2853RingHom, S2853PolyHom, S2853Subst, S2801E37X]

theorem chartZ_Y (K : Type) [Field K] [DecidableEq K] :
    S2853RingHom K (S2801E37Y K) = - S2801E37Y K - 1 := by
  simp [S2853RingHom, S2853PolyHom, S2853Subst, S2801E37Y]

theorem g1Ring_eq_alpha_chartZNeg (K : Type) [Field K] [DecidableEq K] :
    g1Ring K = (alpha K).comp (S2853RingHom K) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply]
    rw [show Ideal.Quotient.mk (S2801E37Ideal K) (MvPolynomial.C a) = algebraMap K (R0 K) a from
      Ideal.Quotient.mk_algebraMap K (I := S2801E37Ideal K) a]
    have h1 : g1Ring K (algebraMap K (R0 K) a) = algebraMap K (Localization.Away (tY K)) a := by
      rw [← Ideal.Quotient.mk_algebraMap K (I := S2801E37Ideal K) a]
      simp [g1Ring, g1Poly, MvPolynomial.eval₂Hom_C]
    have h2 : (alpha K) (S2853RingHom K (algebraMap K (R0 K) a)) =
        algebraMap K (A1 K) a := by
      rw [← Ideal.Quotient.mk_algebraMap K (I := S2801E37Ideal K) a]
      simp [S2853RingHom, S2853PolyHom, alpha, alphaPoly,
        MvPolynomial.eval₂Hom_C]
    rw [h1, h2]
  · intro i
    fin_cases i
    · simp only [RingHom.comp_apply]
      change g1Ring K (S2801E37X K) = (alpha K) (S2853RingHom K (S2801E37X K))
      rw [g1Ring_X, chartZ_X, alpha_X]
    · simp only [RingHom.comp_apply]
      change g1Ring K (S2801E37Y K) = (alpha K) (S2853RingHom K (S2801E37Y K))
      rw [g1Ring_Y, chartZ_Y, map_sub, map_neg, map_one, alpha_S2801E37Y]
      ring

/-! ## 5. The second ring lemma hZ -/

theorem hZ (K : Type) [Field K] [DecidableEq K] :
    (φZ K).comp (g1Ring K) =
      (φZ K).comp ((alpha K).comp (S2853RingHom K)) := by
  have h : g1Ring K = (alpha K).comp (S2853RingHom K) := g1Ring_eq_alpha_chartZNeg K
  rw [h]

#print axioms hY
#print axioms hZ

end LeanFormal.IUT.XiFPaper.S2856HfYZRingActual
end
