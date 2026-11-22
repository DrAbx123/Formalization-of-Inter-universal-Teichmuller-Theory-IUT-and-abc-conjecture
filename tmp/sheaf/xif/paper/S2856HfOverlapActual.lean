import tmp.sheaf.xif.paper.S2855ChartYDirectedCoverActual
import Mathlib.AlgebraicGeometry.Pullbacks

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2853ChartYNegationActual
open LeanFormal.IUT.XiFPaper.S2855ChartYDirectedCoverActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2856HfOverlapActual

variable (K : Type) [Field K]

noncomputable abbrev overlapRing : Type :=
  TensorProduct (E37ChartYRing K) (S2853ChartYNegRing K)
    (Localization.Away (tY K))

noncomputable abbrev overlapSpec : Scheme :=
  Spec (CommRingCat.of (overlapRing K))

noncomputable def pullbackOverlapIso :
    pullback (f0 K) (f1 K) ≅ overlapSpec K :=
  pullbackSpecIso (E37ChartYRing K) (S2853ChartYNegRing K)
    (Localization.Away (tY K))

def HfOverlapRing : Prop :=
  (pullbackOverlapIso K).inv ≫ pullback.fst (f0 K) (f1 K) ≫ g0Scheme K =
    (pullbackOverlapIso K).inv ≫ pullback.snd (f0 K) (f1 K) ≫ g1Scheme K

theorem hf_of_overlapRing (h : HfOverlapRing K) :
    pullback.fst (f0 K) (f1 K) ≫ g0Scheme K =
      pullback.snd (f0 K) (f1 K) ≫ g1Scheme K := by
  have h' := congrArg
    (fun t => (pullbackOverlapIso K).hom ≫ t) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h'

theorem g0Ring_apply_t :
    g0Ring K (S2853ChartYT K) = S2853ChartYNegT K := by
  change S2853G0Poly K (MvPolynomial.X 1) = S2853ChartYNegT K
  exact S2853_hX1 K

theorem g0Ring_apply_s :
    g0Ring K (S2853ChartYS K) = S2853ChartYNegS K := by
  change S2853G0Poly K (MvPolynomial.X 0) = S2853ChartYNegS K
  exact S2853_hX0 K

theorem g0Ring_one_add_t :
    g0Ring K (1 + S2853ChartYT K) *
      algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
        (1 + S2853ChartYT K) = 1 := by
  let B : S2853ChartYNegRing K :=
    algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K)
  let U : S2853ChartYNegRing K :=
    algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (1 + S2853ChartYT K)
  let v : S2853ChartYNegRing K := ↑((S2853ChartYNegUnit K)⁻¹)
  have hA : algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
      (-S2853ChartYT K) = -B := by simp [B]
  have hUeq : U = 1 + B := by simp [U, B, map_add]
  have hvU : v * U = 1 := by
    rw [show U = ↑(S2853ChartYNegUnit K) from (IsUnit.unit_spec _).symm]
    exact Units.inv_mul (S2853ChartYNegUnit K)
  rw [map_add, map_one, g0Ring_apply_t]
  rw [show S2853ChartYNegT K = algebraMap (E37ChartYRing K)
      (S2853ChartYNegRing K) (-S2853ChartYT K) * ↑((S2853ChartYNegUnit K)⁻¹) from rfl]
  rw [show algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
      (1 + S2853ChartYT K) = U from rfl]
  calc
    (1 + algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
        (-S2853ChartYT K) * v) * U
        = U + algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
            (-S2853ChartYT K) * (v * U) := by ring
    _ = U + algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
          (-S2853ChartYT K) := by rw [hvU]; ring
    _ = 1 := by rw [hA, hUeq]; ring

theorem hU : IsUnit (g0Ring K (1 + S2853ChartYT K)) :=
  isUnit_iff_exists_inv.mpr
    ⟨algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
        (1 + S2853ChartYT K), g0Ring_one_add_t K⟩


noncomputable abbrev A1 : Type := E37ChartYOverlapRing K

noncomputable abbrev A2 : Type := Localization.Away (1 + t1 K)

theorem ht1 :
    t1 K = algebraMap (E37ChartYRing K) (A1 K) (tbar K) := by
  rw [t1]
  exact Localization.mk_one_eq_algebraMap (M := Submonoid.powers (tbar K)) (tbar K)

theorem huR1A2 :
    IsUnit (algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K)) := by
  have huA2 : IsUnit (algebraMap (A1 K) (A2 K) (1 + t1 K)) :=
    IsLocalization.Away.algebraMap_isUnit (x := 1 + t1 K)
  have hbridge :
      (algebraMap (A1 K) (A2 K)) ((algebraMap (E37ChartYRing K) (A1 K)) (tbar K))
        = algebraMap (E37ChartYRing K) (A2 K) (tbar K) := by
    simpa using (IsScalarTower.algebraMap_apply
      (E37ChartYRing K) (A1 K) (A2 K) (tbar K)).symm
  have huA2' : IsUnit ((algebraMap (A1 K) (A2 K))
      (1 + (algebraMap (E37ChartYRing K) (A1 K)) (tbar K))) := by
    simpa [ht1 K] using huA2
  rw [map_add, map_one, hbridge] at huA2'
  simpa [map_add, map_one] using huA2'

noncomputable def canon : S2853ChartYNegRing K →+* A2 K :=
  IsLocalization.Away.lift
    (S := S2853ChartYNegRing K)
    (x := 1 + tbar K)
    (g := algebraMap (E37ChartYRing K) (A2 K))
    (huR1A2 K)

noncomputable def uY : E37ChartYRing K →+* A2 K :=
  (canon K).comp (g0Ring K)

theorem huY : IsUnit (uY K (1 + S2853ChartYT K)) :=
  IsUnit.map (canon K) (hU K)

noncomputable def phiY : S2853ChartYNegRing K →+* A2 K :=
  IsLocalization.Away.lift
    (S := S2853ChartYNegRing K)
    (x := 1 + tbar K)
    (g := uY K) (huY K)

#check pullbackOverlapIso
#check HfOverlapRing
#check hf_of_overlapRing
#check hU


/-! ## 2. The two tensor inclusions -/

/-- The left inclusion of the tensor square. -/
noncomputable abbrev incL : S2853ChartYNegRing K →+* overlapRing K :=
  Algebra.TensorProduct.includeLeftRingHom

/-- The right inclusion of the tensor square. -/
noncomputable abbrev incR : E37ChartYOverlapRing K →+* overlapRing K :=
  Algebra.TensorProduct.includeRight.toRingHom

/-- The two inclusions agree on the base ring. -/
theorem incL_algebraMap_eq (r : E37ChartYRing K) :
    incL K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) r) =
      incR K (algebraMap (E37ChartYRing K) (E37ChartYOverlapRing K) r) := by
  have h := RingHom.congr_fun
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := E37ChartYRing K) (A := S2853ChartYNegRing K)
      (B := Localization.Away (tY K))) r
  simpa [incL, incR] using h
/-! ## 3. The chart-Y negation on the overlap -/

/-- uYT : R1 -> S (x) A1 is the chart-Y negation followed by the left inclusion. -/
noncomputable abbrev uYT : E37ChartYRing K →+* overlapRing K :=
  (incL K).comp (g0Ring K)

/-- uZ : R0 -> S (x) A1 is the chart-Z negation followed by the right inclusion. -/
noncomputable abbrev uZ : S2801E37CoordinateRing K →+* overlapRing K :=
  (incR K).comp (g1Ring K)

/-- uYT on the coordinate t, in cleared form. -/
theorem uYT_tY : uYT K (tY K) =
    - (incL K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (tY K))) *
      incL K (↑((S2853ChartYNegUnit K)⁻¹)) := by
  rw [uYT, RingHom.comp_apply, g0Ring_apply_t, S2853ChartYNegT]
  simp only [map_mul, map_neg]

/-- On the overlap 1+t is invertible, coming from the chart-Y negation side. -/
theorem incL_unit_eq : incL K (↑(S2853ChartYNegUnit K)) =
    1 + incR K (algebraMap (E37ChartYRing K) (E37ChartYOverlapRing K) (tY K)) := by
  rw [show (↑(S2853ChartYNegUnit K) : S2853ChartYNegRing K) =
    algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (1 + tY K) from IsUnit.unit_spec _]
  simp only [map_add, map_one, incL_algebraMap_eq K (tY K)]

/-- uYT(t) is a unit. -/
theorem huYT : IsUnit (uYT K (tY K)) := by
  rw [uYT_tY]
  have h1 : IsUnit (incL K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (tY K))) := by
    rw [incL_algebraMap_eq K (tY K)]
    exact IsUnit.map (incR K)
      (IsLocalization.Away.algebraMap_isUnit (x := tY K) (S := E37ChartYOverlapRing K))
  have h2 : IsUnit (incL K (↑((S2853ChartYNegUnit K)⁻¹))) :=
    isUnit_iff_exists_inv.mpr ⟨incL K (↑(S2853ChartYNegUnit K)),
      by rw [← map_mul, Units.inv_mul, map_one]⟩
  exact h1.neg.mul h2

/-- The chart-Y negation, extended from the chart-Y coordinate ring to the
chart-Y overlap D(t). -/
noncomputable def gY : E37ChartYOverlapRing K →+* overlapRing K :=
  IsLocalization.Away.lift (tY K) (huYT K)

theorem gY_comp_algebraMap :
    (gY K).comp (algebraMap (E37ChartYRing K) (E37ChartYOverlapRing K)) = uYT K :=
  IsLocalization.Away.lift_comp (tY K) (huYT K)

theorem gY_apply_s1 : gY K (s1 K) = uYT K (sbar K) := by
  rw [s1_eq_algebraMap K]
  exact IsLocalization.Away.lift_eq (tY K) (huYT K) (sbar K)

theorem gY_apply_t1 : gY K (t1 K) = uYT K (tbar K) := by
  rw [t1_eq_algebraMap K]
  exact IsLocalization.Away.lift_eq (tY K) (huYT K) (tbar K)

/-! ## 4. Values of the chart-Y negation on the overlap, in cleared form -/

theorem gY_s1_mul_uUnit :
    gY K (s1 K) * incL K (↑(S2853ChartYNegUnit K)) = -(incR K (s1 K)) := by
  have hU : incL K (↑((S2853ChartYNegUnit K)⁻¹)) * incL K (↑(S2853ChartYNegUnit K)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hs : gY K (s1 K) =
      - (incL K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (sbar K))) *
        incL K (↑((S2853ChartYNegUnit K)⁻¹)) := by
    rw [gY_apply_s1, uYT, RingHom.comp_apply, g0Ring_apply_s, S2853ChartYNegS]
    simp only [map_mul, map_neg]
  rw [hs]
  calc (- (incL K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (sbar K))) *
        incL K (↑((S2853ChartYNegUnit K)⁻¹))) * incL K (↑(S2853ChartYNegUnit K))
      = - (incL K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (sbar K))) *
          (incL K (↑((S2853ChartYNegUnit K)⁻¹)) * incL K (↑(S2853ChartYNegUnit K))) := by ring
    _ = - (incL K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (sbar K))) := by
        rw [hU, mul_one]
    _ = - (incR K (algebraMap (E37ChartYRing K) (E37ChartYOverlapRing K) (sbar K))) := by
        rw [incL_algebraMap_eq K (sbar K)]
    _ = - (incR K (s1 K)) := by rw [s1_eq_algebraMap K]

theorem gY_t1_mul_uUnit :
    gY K (t1 K) * incL K (↑(S2853ChartYNegUnit K)) = -(incR K (t1 K)) := by
  have hU : incL K (↑((S2853ChartYNegUnit K)⁻¹)) * incL K (↑(S2853ChartYNegUnit K)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have ht : gY K (t1 K) =
      - (incL K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (tbar K))) *
        incL K (↑((S2853ChartYNegUnit K)⁻¹)) := by
    rw [gY_apply_t1, uYT, RingHom.comp_apply, g0Ring_apply_t, S2853ChartYNegT]
    simp only [map_mul, map_neg]
  rw [ht]
  calc (- (incL K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (tbar K))) *
        incL K (↑((S2853ChartYNegUnit K)⁻¹))) * incL K (↑(S2853ChartYNegUnit K))
      = - (incL K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (tbar K))) *
          (incL K (↑((S2853ChartYNegUnit K)⁻¹)) * incL K (↑(S2853ChartYNegUnit K))) := by ring
    _ = - (incL K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (tbar K))) := by
        rw [hU, mul_one]
    _ = - (incR K (algebraMap (E37ChartYRing K) (E37ChartYOverlapRing K) (tbar K))) := by
        rw [incL_algebraMap_eq K (tbar K)]
    _ = - (incR K (t1 K)) := by rw [t1_eq_algebraMap K]

theorem gY_tInv_mul_tUnit :
    gY K (tInv K) * incR K (t1 K) = -(incL K (↑(S2853ChartYNegUnit K))) := by
  have ht : gY K (tInv K) * gY K (t1 K) = 1 := by
    rw [← map_mul, tInv_mul_t1 K, map_one]
  calc gY K (tInv K) * incR K (t1 K)
      = gY K (tInv K) * (- (gY K (t1 K) * incL K (↑(S2853ChartYNegUnit K)))) := by
        rw [gY_t1_mul_uUnit K]; ring
    _ = - (gY K (tInv K) * gY K (t1 K)) * incL K (↑(S2853ChartYNegUnit K)) := by ring
    _ = - (1 * incL K (↑(S2853ChartYNegUnit K))) := by rw [ht]; ring
    _ = - (incL K (↑(S2853ChartYNegUnit K))) := by ring

/-! ## 5. Values of the chart-Z negation -/

theorem tInv_eq_g1Unit_inv :
    tInv K = (↑((g1Unit K)⁻¹) : Localization.Away (tY K)) := by
  have hspec : (↑(g1Unit K) : Localization.Away (tY K)) = t1 K := by
    rw [show (↑(g1Unit K) : Localization.Away (tY K)) =
      algebraMap (E37ChartYRing K) (Localization.Away (tY K)) (tY K) from IsUnit.unit_spec _]
    exact t1_eq_algebraMap K
  have h1 : tInv K * (↑(g1Unit K) : Localization.Away (tY K)) = 1 := by
    rw [hspec]; exact tInv_mul_t1 K
  calc tInv K = tInv K * 1 := by rw [mul_one]
    _ = tInv K * ((↑(g1Unit K) : Localization.Away (tY K)) * ↑((g1Unit K)⁻¹)) := by
        rw [Units.mul_inv]
    _ = (tInv K * (↑(g1Unit K) : Localization.Away (tY K))) * ↑((g1Unit K)⁻¹) := by ring
    _ = 1 * ↑((g1Unit K)⁻¹) := by rw [h1]
    _ = ↑((g1Unit K)⁻¹) := by rw [one_mul]

theorem g1Ring_apply_X : g1Ring K (S2801E37X K) = s1 K * tInv K := by
  simp [g1Ring, g1Poly, g1Vals, S2801E37X, s1_eq_algebraMap, tInv_eq_g1Unit_inv]

theorem g1Ring_apply_Y : g1Ring K (S2801E37Y K) = -1 - tInv K := by
  simp [g1Ring, g1Poly, g1Vals, S2801E37Y, tInv_eq_g1Unit_inv]

theorem alpha_apply_X : alpha K (S2801E37X K) = s1 K * tInv K := by
  simp [alpha, alphaPoly, evalVals, S2801E37X]

theorem alpha_apply_Y : alpha K (S2801E37Y K) = tInv K := by
  simp [alpha, alphaPoly, evalVals, S2801E37Y]

/-! ## 6. The comparison identity gY.comp alpha = uZ -/

theorem g0Ring_algebraMap_K (a : K) :
    g0Ring K (algebraMap K (E37ChartYRing K) a) =
      algebraMap K (S2853ChartYNegRing K) a := by
  rw [← Ideal.Quotient.mk_algebraMap K (I := E37ChartYIdeal K)]
  change MvPolynomial.eval₂Hom (algebraMap K (S2853ChartYNegRing K)) (S2853G0Vals K)
    (algebraMap K (MvPolynomial (Fin 2) K) a) = algebraMap K (S2853ChartYNegRing K) a
  rw [MvPolynomial.algebraMap_eq]
  exact MvPolynomial.eval₂Hom_C _ _ a

theorem g1Ring_algebraMap_K (a : K) :
    g1Ring K (algebraMap K (S2801E37CoordinateRing K) a) =
      algebraMap K (E37ChartYOverlapRing K) a := by
  rw [← Ideal.Quotient.mk_algebraMap K (I := S2801E37Ideal K)]
  change MvPolynomial.eval₂Hom (algebraMap K (Localization.Away (tY K))) (g1Vals K)
    (algebraMap K (MvPolynomial (Fin 2) K) a) = algebraMap K (E37ChartYOverlapRing K) a
  rw [MvPolynomial.algebraMap_eq]
  exact MvPolynomial.eval₂Hom_C _ _ a

theorem alpha_algebraMap_K (a : K) :
    alpha K (algebraMap K (S2801E37CoordinateRing K) a) =
      algebraMap K (E37ChartYOverlapRing K) a := by
  rw [← Ideal.Quotient.mk_algebraMap K (I := S2801E37Ideal K)]
  change MvPolynomial.eval₂Hom (algebraMap K (Localization.Away (tY K))) (evalVals K)
    (algebraMap K (MvPolynomial (Fin 2) K) a) = algebraMap K (E37ChartYOverlapRing K) a
  rw [MvPolynomial.algebraMap_eq]
  exact MvPolynomial.eval₂Hom_C _ _ a

theorem mk_C_eq (a : K) :
    Ideal.Quotient.mk (S2801E37Ideal K) (MvPolynomial.C a) =
      algebraMap K (S2801E37CoordinateRing K) a := by
  rw [← MvPolynomial.algebraMap_eq]
  exact Ideal.Quotient.mk_algebraMap K (I := S2801E37Ideal K) a

theorem gY_algebraMap_K (a : K) :
    gY K (algebraMap K (E37ChartYOverlapRing K) a) =
      incR K (algebraMap K (E37ChartYOverlapRing K) a) := by
  have hL : gY K (algebraMap K (E37ChartYOverlapRing K) a) =
      incL K (algebraMap K (S2853ChartYNegRing K) a) := by
    rw [IsScalarTower.algebraMap_apply K (E37ChartYRing K) (E37ChartYOverlapRing K) a]
    rw [show gY K (algebraMap (E37ChartYRing K) (E37ChartYOverlapRing K)
          (algebraMap K (E37ChartYRing K) a)) =
        uYT K (algebraMap K (E37ChartYRing K) a) from
      IsLocalization.Away.lift_eq (tY K) (huYT K) _]
    rw [uYT, RingHom.comp_apply, g0Ring_algebraMap_K,
      IsScalarTower.algebraMap_apply K (E37ChartYRing K) (S2853ChartYNegRing K) a]
  have hR : incR K (algebraMap K (E37ChartYOverlapRing K) a) =
      incL K (algebraMap K (S2853ChartYNegRing K) a) := by
    rw [IsScalarTower.algebraMap_apply K (E37ChartYRing K) (E37ChartYOverlapRing K) a,
      IsScalarTower.algebraMap_apply K (E37ChartYRing K) (S2853ChartYNegRing K) a]
    exact (incL_algebraMap_eq K (algebraMap K (E37ChartYRing K) a)).symm
  rw [hL, hR]

theorem gY_s1_mul_tInv : gY K (s1 K * tInv K) = incR K (s1 K * tInv K) := by
  have hT : IsUnit (incR K (t1 K)) :=
    isUnit_iff_exists_inv.mpr ⟨incR K (tInv K), by rw [← map_mul, t1_mul_tInv K, map_one]⟩
  have hU : IsUnit (incL K (↑(S2853ChartYNegUnit K))) :=
    isUnit_iff_exists_inv.mpr ⟨incL K (↑((S2853ChartYNegUnit K)⁻¹)),
      by rw [← map_mul, Units.mul_inv, map_one]⟩
  refine (IsUnit.mul_left_inj (hT.mul hU)).mp ?_
  rw [map_mul (gY K)]
  have hR : incR K (s1 K * tInv K) * (incR K (t1 K) * incL K (↑(S2853ChartYNegUnit K))) =
      incR K (s1 K) * incL K (↑(S2853ChartYNegUnit K)) := by
    rw [map_mul (incR K)]
    have ht : incR K (tInv K) * incR K (t1 K) = 1 := by
      rw [← map_mul, tInv_mul_t1 K, map_one]
    calc incR K (s1 K) * incR K (tInv K) * (incR K (t1 K) * incL K (↑(S2853ChartYNegUnit K)))
        = incR K (s1 K) * (incR K (tInv K) * incR K (t1 K)) *
            incL K (↑(S2853ChartYNegUnit K)) := by ring
      _ = incR K (s1 K) * 1 * incL K (↑(S2853ChartYNegUnit K)) := by rw [ht]
      _ = incR K (s1 K) * incL K (↑(S2853ChartYNegUnit K)) := by ring
  have hL : gY K (s1 K) * gY K (tInv K) *
        (incR K (t1 K) * incL K (↑(S2853ChartYNegUnit K))) =
      incR K (s1 K) * incL K (↑(S2853ChartYNegUnit K)) := by
    calc gY K (s1 K) * gY K (tInv K) *
          (incR K (t1 K) * incL K (↑(S2853ChartYNegUnit K)))
        = (gY K (s1 K) * incL K (↑(S2853ChartYNegUnit K))) *
            (gY K (tInv K) * incR K (t1 K)) := by ring
      _ = (- (incR K (s1 K))) * (- (incL K (↑(S2853ChartYNegUnit K)))) := by
          rw [gY_s1_mul_uUnit K, gY_tInv_mul_tUnit K]
      _ = incR K (s1 K) * incL K (↑(S2853ChartYNegUnit K)) := by ring
  rw [hL, hR]

theorem gY_tInv_eq : gY K (tInv K) = incR K (-1 - tInv K) := by
  have hT : IsUnit (incR K (t1 K)) :=
    isUnit_iff_exists_inv.mpr ⟨incR K (tInv K), by rw [← map_mul, t1_mul_tInv K, map_one]⟩
  refine (IsUnit.mul_left_inj hT).mp ?_
  rw [gY_tInv_mul_tUnit K]
  have hR : incR K (-1 - tInv K) * incR K (t1 K) = -(incL K (↑(S2853ChartYNegUnit K))) := by
    rw [← map_mul]
    have h1 : (-1 - tInv K) * t1 K = -t1 K - 1 := by
      rw [sub_mul, neg_mul, one_mul, tInv_mul_t1 K]
    rw [h1, map_sub, map_neg, map_one, incL_unit_eq K, t1_eq_algebraMap K]
    ring
  rw [hR]

theorem gY_comp_alpha : (gY K).comp (alpha K) = uZ K := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply]
    rw [mk_C_eq K a,
      alpha_algebraMap_K K a, gY_algebraMap_K K a, g1Ring_algebraMap_K K a]
  · intro i
    fin_cases i
    · change gY K (alpha K (S2801E37X K)) = uZ K (S2801E37X K)
      rw [alpha_apply_X, gY_s1_mul_tInv, RingHom.comp_apply, g1Ring_apply_X]
    · change gY K (alpha K (S2801E37Y K)) = uZ K (S2801E37Y K)
      rw [alpha_apply_Y, gY_tInv_eq, RingHom.comp_apply, g1Ring_apply_Y]

/-! ## 7. The gluing condition between the two charts -/

theorem phi_comp_algebraMap :
    (phi K).comp (algebraMap (S2801E37CoordinateRing K) (E37ChartZOverlapRing K)) = alpha K := by
  simpa [phi] using IsLocalization.Away.lift_comp (R := S2801E37CoordinateRing K)
    (S := E37ChartZOverlapRing K) (x := S2801E37Y K) (g := alpha K) (alpha_S2801E37Y_isUnit K)

/-- Spec.map of a composite ring map is the composite of the Spec.map s. -/
theorem specMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) =
      Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The gluing condition of the projective glue data, in the form used below:
the chart-Y overlap embeds into the glued scheme compatibly with the chart-Z side. -/
theorem glue_condition_formula :
    E37ChartYOverlapMap K ≫ S2820E37ChartYMap K =
      Spec.map (CommRingCat.ofHom (alpha K)) ≫ S2820E37ChartZMap K := by
  have h := (E37ProjGlueData K (S2820E37TransitionIso K)).glue_condition
    (ULift.up true) (ULift.up false)
  have h' : (S2820E37TransitionIso K).inv ≫ E37ChartZOverlapMap K ≫ S2820E37ChartZMap K =
      E37ChartYOverlapMap K ≫ S2820E37ChartYMap K := by
    simpa [E37ProjGlueData, E37ProjT, E37ProjF, S2820E37ChartYMap, S2820E37ChartZMap,
      S2820E37ProjectiveScheme, E37ProjChartYMap, E37ProjChartZMap] using h
  rw [← h']
  have hinv : (S2820E37TransitionIso K).inv =
      Spec.map (CommRingCat.ofHom (phi K)) := rfl
  rw [hinv]
  rw [show E37ChartZOverlapMap K =
      Spec.map (CommRingCat.ofHom (algebraMap (S2801E37CoordinateRing K)
        (E37ChartZOverlapRing K))) from rfl]
  rw [← Category.assoc, ← specMap_comp_ringHom (algebraMap (S2801E37CoordinateRing K)
    (E37ChartZOverlapRing K)) (phi K)]
  rw [phi_comp_algebraMap K]

/-! ## 8. The overlap compatibility -/

theorem hfRing : HfOverlapRing K := by
  unfold HfOverlapRing
  have hL : (pullbackOverlapIso K).inv ≫ pullback.fst (f0 K) (f1 K) ≫ g0Scheme K =
      Spec.map (CommRingCat.ofHom (uYT K)) ≫ S2820E37ChartYMap K := by
    rw [show pullbackOverlapIso K = pullbackSpecIso (E37ChartYRing K) (S2853ChartYNegRing K)
      (Localization.Away (tY K)) from rfl]
    rw [← Category.assoc, pullbackSpecIso_inv_fst]
    unfold g0Scheme
    rw [← Category.assoc, ← specMap_comp_ringHom (g0Ring K) (incL K)]
  have hR : (pullbackOverlapIso K).inv ≫ pullback.snd (f0 K) (f1 K) ≫ g1Scheme K =
      Spec.map (CommRingCat.ofHom (uZ K)) ≫ S2820E37ChartZMap K := by
    rw [show pullbackOverlapIso K = pullbackSpecIso (E37ChartYRing K) (S2853ChartYNegRing K)
      (Localization.Away (tY K)) from rfl]
    rw [← Category.assoc, pullbackSpecIso_inv_snd]
    unfold g1Scheme
    rw [← Category.assoc]
    exact congrArg (fun t => t ≫ S2820E37ChartZMap K)
      (specMap_comp_ringHom (g1Ring K) (incR K)).symm
  rw [hL, hR]
  calc Spec.map (CommRingCat.ofHom (uYT K)) ≫ S2820E37ChartYMap K
      = Spec.map (CommRingCat.ofHom ((gY K).comp
          (algebraMap (E37ChartYRing K) (E37ChartYOverlapRing K)))) ≫ S2820E37ChartYMap K := by
        rw [← gY_comp_algebraMap K]
    _ = (Spec.map (CommRingCat.ofHom (gY K)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (E37ChartYRing K) (E37ChartYOverlapRing K)))) ≫
          S2820E37ChartYMap K := by
        rw [specMap_comp_ringHom (algebraMap (E37ChartYRing K) (E37ChartYOverlapRing K)) (gY K)]
    _ = Spec.map (CommRingCat.ofHom (gY K)) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap (E37ChartYRing K) (E37ChartYOverlapRing K))) ≫
            S2820E37ChartYMap K) := by rw [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom (gY K)) ≫
          (E37ChartYOverlapMap K ≫ S2820E37ChartYMap K) := by rfl
    _ = Spec.map (CommRingCat.ofHom (gY K)) ≫
          (Spec.map (CommRingCat.ofHom (alpha K)) ≫ S2820E37ChartZMap K) := by
        rw [glue_condition_formula K]
    _ = (Spec.map (CommRingCat.ofHom (gY K)) ≫
          Spec.map (CommRingCat.ofHom (alpha K))) ≫ S2820E37ChartZMap K := by rw [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom ((gY K).comp (alpha K))) ≫ S2820E37ChartZMap K := by
        rw [specMap_comp_ringHom (alpha K) (gY K)]
    _ = Spec.map (CommRingCat.ofHom (uZ K)) ≫ S2820E37ChartZMap K := by
        rw [gY_comp_alpha K]

/-! ## 9. All cases of the gluing compatibility -/

local instance : IsOpenImmersion (f0 K) :=
  Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of (E37ChartYRing K))
    (1 + tY K)

local instance : IsOpenImmersion (f1 K) :=
  Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of (E37ChartYRing K)) (tY K)

local instance : Mono (f0 K) := IsOpenImmersion.mono (f0 K)

local instance : Mono (f1 K) := IsOpenImmersion.mono (f1 K)

theorem hf_false_true :
    pullback.fst (f0 K) (f1 K) ≫ g0Scheme K =
      pullback.snd (f0 K) (f1 K) ≫ g1Scheme K :=
  hf_of_overlapRing K (hfRing K)

/-- The gluing compatibility for all pairs of the two chart-Y pieces. -/
theorem hf_pair : ∀ x y,
    pullback.fst ((chartYCover K).f x) ((chartYCover K).f y) ≫ chartYNegGMap K x =
      pullback.snd ((chartYCover K).f x) ((chartYCover K).f y) ≫ chartYNegGMap K y := by
  intro x y
  cases x <;> cases y
  · show pullback.fst (f0 K) (f0 K) ≫ g0Scheme K =
      pullback.snd (f0 K) (f0 K) ≫ g0Scheme K
    rw [fst_eq_snd_of_mono_eq (f0 K)]
  · exact hf_false_true K
  · show pullback.fst (f1 K) (f0 K) ≫ g1Scheme K =
      pullback.snd (f1 K) (f0 K) ≫ g0Scheme K
    have hA : (pullbackSymmetry (f0 K) (f1 K)).hom ≫
          (pullback.fst (f1 K) (f0 K) ≫ g1Scheme K) =
        (pullbackSymmetry (f0 K) (f1 K)).hom ≫
          (pullback.snd (f1 K) (f0 K) ≫ g0Scheme K) := by
      rw [← Category.assoc, pullbackSymmetry_hom_comp_fst, ← Category.assoc,
        pullbackSymmetry_hom_comp_snd]
      exact (hf_false_true K).symm
    have h2 := congrArg (fun t => (pullbackSymmetry (f0 K) (f1 K)).inv ≫ t) hA
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h2
  · show pullback.fst (f1 K) (f1 K) ≫ g1Scheme K =
      pullback.snd (f1 K) (f1 K) ≫ g1Scheme K
    rw [fst_eq_snd_of_mono_eq (f1 K)]

/-- The chart-Y negation morphism to the glued projective scheme, unconditionally. -/
noncomputable def chartYNegGlued : E37ChartYScheme K ⟶ S2820E37ProjectiveScheme K :=
  (chartYCover K).glueMorphisms (chartYNegGMap K) (hf_pair K)

#check hfRing
#check hf_pair
#check chartYNegGlued
#print axioms pullbackOverlapIso
#print axioms hfRing
#print axioms hf_pair
#print axioms chartYNegGlued


end LeanFormal.IUT.XiFPaper.S2856HfOverlapActual
end
