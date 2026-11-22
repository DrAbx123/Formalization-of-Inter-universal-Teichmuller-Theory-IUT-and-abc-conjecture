/-
  The double overlap ring A2 = A1[(1+t1)^-1] of the chart-Y overlap, together
  with the chart-Z projection phiZ, the localization map canon from D(1+t),
  and the two ring maps

    uY   = canon o g0Ring : E37ChartYRing K -> A2, and
    phiY = awayLift uY (1+tbar) : D(1+t) -> A2.

  Main results:
  * hY : phiY o g0Ring = phiZ o (R1 -> A1),
  * hZ : phiZ o g1Ring = phiZ o (alpha o S2853RingHom).

  The proof of hY evaluates both sides on the polynomial generators of R1
  (constants, s and t); the proof of hZ does the same for the chart-Z
  coordinate ring, using g1Ring = (s/t, -1-1/t) and
  alpha o chartZNeg = (x, -y-1) = (s/t, -1-1/t).
-/

import tmp.sheaf.xif.paper.S2855ChartYDirectedCoverActual
import tmp.sheaf.xif.paper.S2820E37TransitionActual
import tmp.sheaf.xif.paper.S2853E37NegationAutomorphismActual
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2853ChartYNegationActual
open LeanFormal.IUT.XiFPaper.S2855ChartYDirectedCoverActual
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2856HfRingActual

abbrev A2 (K : Type) [Field K] : Type := Localization.Away (1 + t1 K)

noncomputable def phiZ (K : Type) [Field K] : A1 K →+* A2 K :=
  algebraMap (A1 K) (A2 K)

theorem hu (K : Type) [Field K] :
    IsUnit (algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K)) := by
  have h : algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K) =
      algebraMap (A1 K) (A2 K) (1 + t1 K) := by
    rw [IsScalarTower.algebraMap_apply (E37ChartYRing K) (A1 K) (A2 K)]
    congr 1
    rw [map_add, map_one, t1_eq_algebraMap K]
  rw [h]
  exact IsLocalization.Away.algebraMap_isUnit (x := 1 + t1 K) (S := A2 K)

theorem phiZ_algebraMap (K : Type) [Field K] (r : E37ChartYRing K) :
    phiZ K (algebraMap (E37ChartYRing K) (A1 K) r) =
      algebraMap (E37ChartYRing K) (A2 K) r := by
  show algebraMap (A1 K) (A2 K) (algebraMap (E37ChartYRing K) (A1 K) r) =
    algebraMap (E37ChartYRing K) (A2 K) r
  exact (IsScalarTower.algebraMap_apply (E37ChartYRing K) (A1 K) (A2 K) r).symm

theorem phiZ_algebraMap_K (K : Type) [Field K] (a : K) :
    phiZ K (algebraMap K (A1 K) a) = algebraMap K (A2 K) a := by
  show algebraMap (A1 K) (A2 K) (algebraMap K (A1 K) a) = algebraMap K (A2 K) a
  exact (IsScalarTower.algebraMap_apply K (A1 K) (A2 K) a).symm

theorem phiZ_s1 (K : Type) [Field K] :
    phiZ K (s1 K) = algebraMap (E37ChartYRing K) (A2 K) (sY K) := by
  rw [s1_eq_algebraMap K]
  exact phiZ_algebraMap K (sbar K)

theorem phiZ_t1 (K : Type) [Field K] :
    phiZ K (t1 K) = algebraMap (E37ChartYRing K) (A2 K) (tY K) :=
  calc phiZ K (t1 K) =
        phiZ K (algebraMap (E37ChartYRing K) (A1 K) (tbar K)) :=
        congrArg (phiZ K) (t1_eq_algebraMap K)
    _ = algebraMap (E37ChartYRing K) (A2 K) (tY K) := phiZ_algebraMap K (tbar K)

noncomputable def canon (K : Type) [Field K] : S2853ChartYNegRing K →+* A2 K :=
  IsLocalization.Away.lift (S := S2853ChartYNegRing K) (x := 1 + tbar K)
    (g := algebraMap (E37ChartYRing K) (A2 K)) (hu K)

theorem canon_comp (K : Type) [Field K] :
    (canon K).comp (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)) =
      algebraMap (E37ChartYRing K) (A2 K) := by
  simpa [canon] using IsLocalization.Away.lift_comp
    (R := E37ChartYRing K) (S := S2853ChartYNegRing K) (x := 1 + tbar K)
    (g := algebraMap (E37ChartYRing K) (A2 K)) (hu K)

theorem canon_algebraMap (K : Type) [Field K] (r : E37ChartYRing K) :
    canon K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) r) =
      algebraMap (E37ChartYRing K) (A2 K) r :=
  RingHom.congr_fun (canon_comp K) r

theorem canon_algebraMap_K (K : Type) [Field K] (a : K) :
    canon K (algebraMap K (S2853ChartYNegRing K) a) = algebraMap K (A2 K) a := by
  rw [IsScalarTower.algebraMap_apply K (E37ChartYRing K) (S2853ChartYNegRing K)]
  rw [canon_algebraMap]
  exact (IsScalarTower.algebraMap_apply K (E37ChartYRing K) (A2 K) a).symm

noncomputable def uY (K : Type) [Field K] : E37ChartYRing K →+* A2 K :=
  (canon K).comp (g0Ring K)

theorem g0Ring_apply_s (K : Type) [Field K] :
    g0Ring K (sY K) = S2853ChartYNegS K := by
  change S2853G0Poly K (MvPolynomial.X 0) = S2853ChartYNegS K
  exact S2853_hX0 K

theorem g0Ring_apply_t (K : Type) [Field K] :
    g0Ring K (tY K) = S2853ChartYNegT K := by
  change S2853G0Poly K (MvPolynomial.X 1) = S2853ChartYNegT K
  exact S2853_hX1 K

theorem g0Ring_algebraMap (K : Type) [Field K] (a : K) :
    g0Ring K (algebraMap K (E37ChartYRing K) a) =
      algebraMap K (S2853ChartYNegRing K) a := by
  rw [← Ideal.Quotient.mk_algebraMap K (I := E37ChartYIdeal K) a]
  change S2853G0Poly K (algebraMap K (MvPolynomial (Fin 2) K) a) =
    algebraMap K (S2853ChartYNegRing K) a
  rw [show algebraMap K (MvPolynomial (Fin 2) K) a = MvPolynomial.C a from rfl]
  simp [S2853G0Poly]

noncomputable abbrev negUnit (K : Type) [Field K] : S2853ChartYNegRing K :=
  ↑(S2853ChartYNegUnit K)

noncomputable abbrev negUnitInv (K : Type) [Field K] : S2853ChartYNegRing K :=
  ↑((S2853ChartYNegUnit K)⁻¹)

theorem negUnit_spec (K : Type) [Field K] :
    negUnit K = algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (1 + tbar K) :=
  IsUnit.unit_spec _

theorem negUnitInv_mul_negUnit (K : Type) [Field K] :
    negUnitInv K * negUnit K = 1 := by
  simpa [negUnit, negUnitInv] using Units.inv_mul (S2853ChartYNegUnit K)

theorem negUnit_mul_negUnitInv (K : Type) [Field K] :
    negUnit K * negUnitInv K = 1 := by
  simpa [negUnit, negUnitInv] using Units.mul_inv (S2853ChartYNegUnit K)

theorem negS_eq (K : Type) [Field K] :
    S2853ChartYNegS K =
      -(algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (sY K)) * negUnitInv K := by
  simp [S2853ChartYNegS, negUnitInv, sY]

theorem negT_eq (K : Type) [Field K] :
    S2853ChartYNegT K =
      -(algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (tY K)) * negUnitInv K := by
  simp [S2853ChartYNegT, negUnitInv, tY]

theorem g0Ring_one_add_t (K : Type) [Field K] :
    g0Ring K (1 + tbar K) *
      algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (1 + tbar K) = 1 := by
  let B : S2853ChartYNegRing K :=
    algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (tbar K)
  let U : S2853ChartYNegRing K :=
    algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (1 + tbar K)
  let v : S2853ChartYNegRing K := ↑((S2853ChartYNegUnit K)⁻¹)
  have hUeq : U = 1 + B := by simp [U, B, map_add]
  have hvU : v * U = 1 := by
    rw [show U = ↑(S2853ChartYNegUnit K) from (IsUnit.unit_spec _).symm]
    exact Units.inv_mul (S2853ChartYNegUnit K)
  rw [map_add, map_one, g0Ring_apply_t K]
  rw [show S2853ChartYNegT K =
    algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (-(tbar K)) * v from rfl]
  rw [show algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (1 + tbar K) = U from rfl]
  calc
    (1 + algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (-(tbar K)) * v) * U
        = U + algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (-(tbar K)) * (v * U) := by
          ring
    _ = U + algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (-(tbar K)) := by
          rw [hvU]; ring
    _ = 1 := by rw [hUeq]; rw [map_neg]; ring

theorem uY_one_add_mul (K : Type) [Field K] :
    uY K (1 + tbar K) * algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K) = 1 := by
  show canon K (g0Ring K (1 + tbar K)) *
    algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K) = 1
  have h := congrArg (canon K) (g0Ring_one_add_t K)
  simp only [map_mul, map_one] at h
  rwa [show canon K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (1 + tbar K)) =
    algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K) from canon_algebraMap K (1 + tbar K)] at h

theorem huY (K : Type) [Field K] : IsUnit (uY K (1 + tbar K)) :=
  isUnit_iff_exists_inv.mpr
    ⟨algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K), uY_one_add_mul K⟩

theorem uY_s (K : Type) [Field K] :
    uY K (sY K) = -(algebraMap (E37ChartYRing K) (A2 K) (sY K)) * canon K (negUnitInv K) := by
  show canon K (g0Ring K (sY K)) = _
  rw [g0Ring_apply_s K, negS_eq K]
  rw [map_mul, map_neg, canon_algebraMap]

theorem uY_t (K : Type) [Field K] :
    uY K (tY K) = -(algebraMap (E37ChartYRing K) (A2 K) (tY K)) * canon K (negUnitInv K) := by
  show canon K (g0Ring K (tY K)) = _
  rw [g0Ring_apply_t K, negT_eq K]
  rw [map_mul, map_neg, canon_algebraMap]

theorem canon_negUnitInv_mul (K : Type) [Field K] :
    canon K (negUnitInv K) * algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K) = 1 := by
  have h := congrArg (canon K) (negUnitInv_mul_negUnit K)
  simp only [map_mul, map_one] at h
  rwa [show canon K (negUnit K) = algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K) from by
    rw [negUnit_spec]; exact canon_algebraMap K (1 + tbar K)] at h

noncomputable def phiY (K : Type) [Field K] : S2853ChartYNegRing K →+* A2 K :=
  Localization.awayLift (uY K) (1 + tbar K) (huY K)

theorem phiY_comp (K : Type) [Field K] :
    (phiY K).comp (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)) = uY K := by
  simpa [phiY] using (IsLocalization.Away.lift_comp
    (R := E37ChartYRing K) (S := S2853ChartYNegRing K) (x := 1 + tbar K)
    (g := uY K) (huY K))

theorem phiY_algebraMap (K : Type) [Field K] (r : E37ChartYRing K) :
    phiY K (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) r) = uY K r :=
  RingHom.congr_fun (phiY_comp K) r

theorem phiY_negUnit (K : Type) [Field K] :
    phiY K (negUnit K) = uY K (1 + tbar K) := by
  rw [negUnit_spec]
  exact phiY_algebraMap K (1 + tbar K)

theorem phiY_negUnitInv (K : Type) [Field K] :
    phiY K (negUnitInv K) = algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K) := by
  have h1 : phiY K (negUnit K) = uY K (1 + tbar K) := phiY_negUnit K
  have h2 : uY K (1 + tbar K) * algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K) = 1 :=
    uY_one_add_mul K
  have h3 : phiY K (negUnitInv K) * phiY K (negUnit K) = 1 := by
    rw [← map_mul, negUnitInv_mul_negUnit, map_one]
  calc phiY K (negUnitInv K)
      = phiY K (negUnitInv K) * 1 := (mul_one _).symm
    _ = phiY K (negUnitInv K) *
          (phiY K (negUnit K) * algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K)) := by
          rw [h1, h2]
    _ = (phiY K (negUnitInv K) * phiY K (negUnit K)) *
          algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K) := by ring
    _ = 1 * algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K) := by rw [h3]
    _ = algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K) := by ring

theorem phiY_negS (K : Type) [Field K] :
    phiY K (S2853ChartYNegS K) = algebraMap (E37ChartYRing K) (A2 K) (sY K) := by
  have hU := phiY_negUnitInv K
  have hu := uY_s K
  have hc := canon_negUnitInv_mul K
  rw [negS_eq K]
  rw [map_mul, map_neg, phiY_algebraMap, hU, hu]
  calc -(-(algebraMap (E37ChartYRing K) (A2 K) (sY K)) * canon K (negUnitInv K)) *
        algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K)
      = algebraMap (E37ChartYRing K) (A2 K) (sY K) *
          (canon K (negUnitInv K) * algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K)) := by
          ring
    _ = algebraMap (E37ChartYRing K) (A2 K) (sY K) * 1 := by rw [hc]
    _ = algebraMap (E37ChartYRing K) (A2 K) (sY K) := by ring

theorem phiY_negT (K : Type) [Field K] :
    phiY K (S2853ChartYNegT K) = algebraMap (E37ChartYRing K) (A2 K) (tY K) := by
  have hU := phiY_negUnitInv K
  have hu := uY_t K
  have hc := canon_negUnitInv_mul K
  rw [negT_eq K]
  rw [map_mul, map_neg, phiY_algebraMap, hU, hu]
  calc -(-(algebraMap (E37ChartYRing K) (A2 K) (tY K)) * canon K (negUnitInv K)) *
        algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K)
      = algebraMap (E37ChartYRing K) (A2 K) (tY K) *
          (canon K (negUnitInv K) * algebraMap (E37ChartYRing K) (A2 K) (1 + tbar K)) := by
          ring
    _ = algebraMap (E37ChartYRing K) (A2 K) (tY K) * 1 := by rw [hc]
    _ = algebraMap (E37ChartYRing K) (A2 K) (tY K) := by ring

theorem phiY_algebraMap_K (K : Type) [Field K] (a : K) :
    phiY K (algebraMap K (S2853ChartYNegRing K) a) = algebraMap K (A2 K) a := by
  rw [IsScalarTower.algebraMap_apply K (E37ChartYRing K) (S2853ChartYNegRing K)]
  rw [phiY_algebraMap]
  show canon K (g0Ring K (algebraMap K (E37ChartYRing K) a)) = algebraMap K (A2 K) a
  rw [g0Ring_algebraMap]
  exact canon_algebraMap_K K a

theorem hY (K : Type) [Field K] :
    (phiY K).comp (g0Ring K) =
      (phiZ K).comp (algebraMap (E37ChartYRing K) (A1 K)) := by
  have hL : ((phiY K).comp (g0Ring K)).comp (Ideal.Quotient.mk (E37ChartYIdeal K)) =
      (phiY K).comp (g0Poly K) := by
    apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply]
    rfl
  have hR : ((phiZ K).comp (algebraMap (E37ChartYRing K) (A1 K))).comp
        (Ideal.Quotient.mk (E37ChartYIdeal K)) =
      (phiZ K).comp (deltaPoly K) := by
    apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply]
    rw [deltaPoly_apply K p]
  apply Ideal.Quotient.ringHom_ext
  rw [hL, hR]
  apply MvPolynomial.ringHom_ext
  · intro a
    change phiY K (g0Poly K (MvPolynomial.C a)) = phiZ K (deltaPoly K (MvPolynomial.C a))
    have hL : g0Poly K (MvPolynomial.C a) = algebraMap K (S2853ChartYNegRing K) a := by
      simp [g0Poly, S2853G0Poly]
    have hR : deltaPoly K (MvPolynomial.C a) = algebraMap K (A1 K) a := by
      simp [deltaPoly]
    rw [hL, hR, phiY_algebraMap_K, phiZ_algebraMap_K]
  · intro i
    fin_cases i
    · change phiY K (g0Poly K (MvPolynomial.X 0)) = phiZ K (deltaPoly K (MvPolynomial.X 0))
      rw [show g0Poly K (MvPolynomial.X 0) = S2853ChartYNegS K from S2853_hX0 K]
      rw [show deltaPoly K (MvPolynomial.X 0) = s1 K from by simp [deltaPoly]]
      rw [phiY_negS, phiZ_s1]
    · change phiY K (g0Poly K (MvPolynomial.X 1)) = phiZ K (deltaPoly K (MvPolynomial.X 1))
      rw [show g0Poly K (MvPolynomial.X 1) = S2853ChartYNegT K from S2853_hX1 K]
      rw [show deltaPoly K (MvPolynomial.X 1) = t1 K from by simp [deltaPoly]]
      rw [phiY_negT, phiZ_t1]

theorem g1Poly_C (K : Type) [Field K] (a : K) :
    g1Poly K (MvPolynomial.C a) = algebraMap K (Localization.Away (tY K)) a := by
  simp [g1Poly]

theorem g1Poly_X0 (K : Type) [Field K] :
    g1Poly K (MvPolynomial.X 0) =
      algebraMap (E37ChartYRing K) (Localization.Away (tY K)) (sY K) *
        (↑((g1Unit K)⁻¹) : Localization.Away (tY K)) := by
  simp [g1Poly, g1Vals]

theorem g1Poly_X1 (K : Type) [Field K] :
    g1Poly K (MvPolynomial.X 1) = -1 - (↑((g1Unit K)⁻¹) : Localization.Away (tY K)) := by
  simp [g1Poly, g1Vals]

theorem g1Unit_coe (K : Type) [Field K] :
    (↑(g1Unit K) : Localization.Away (tY K)) = t1 K := by
  rw [show (↑(g1Unit K) : Localization.Away (tY K)) =
    algebraMap (E37ChartYRing K) (Localization.Away (tY K)) (tY K) from IsUnit.unit_spec _]
  exact (t1_eq_algebraMap K).symm

theorem g1UnitInv_eq_tInv (K : Type) [Field K] :
    (↑((g1Unit K)⁻¹) : Localization.Away (tY K)) = tInv K := by
  have hw : (↑(g1Unit K) : Localization.Away (tY K)) = t1 K := g1Unit_coe K
  have hzw : (↑((g1Unit K)⁻¹) : Localization.Away (tY K)) * t1 K = 1 := by
    rw [← hw]
    exact Units.inv_mul (g1Unit K)
  calc (↑((g1Unit K)⁻¹) : Localization.Away (tY K))
      = (↑((g1Unit K)⁻¹) : Localization.Away (tY K)) * 1 := (mul_one _).symm
    _ = (↑((g1Unit K)⁻¹) : Localization.Away (tY K)) * (t1 K * tInv K) := by
          rw [t1_mul_tInv K]
    _ = ((↑((g1Unit K)⁻¹) : Localization.Away (tY K)) * t1 K) * tInv K := by ring
    _ = 1 * tInv K := by rw [hzw]
    _ = tInv K := by ring

theorem g1Poly_X0' (K : Type) [Field K] :
    g1Poly K (MvPolynomial.X 0) = algebraMap (E37ChartYRing K) (A1 K) (sY K) * tInv K := by
  rw [g1Poly_X0 K, g1UnitInv_eq_tInv K]

theorem g1Poly_X1' (K : Type) [Field K] :
    g1Poly K (MvPolynomial.X 1) = -1 - tInv K := by
  rw [g1Poly_X1 K, g1UnitInv_eq_tInv K]

theorem g1Ring_comp_mk (K : Type) [Field K] :
    (g1Ring K).comp (Ideal.Quotient.mk (S2801E37Ideal K)) = g1Poly K :=
  RingHom.ext (fun p => rfl)

theorem alphaPoly_C (K : Type) [Field K] (a : K) :
    alphaPoly K (MvPolynomial.C a) = algebraMap K (A1 K) a := by
  simp [alphaPoly]

theorem alphaPoly_X0 (K : Type) [Field K] :
    alphaPoly K (MvPolynomial.X 0) = s1 K * tInv K := by
  simp [alphaPoly, evalVals]

theorem alphaPoly_X1 (K : Type) [Field K] :
    alphaPoly K (MvPolynomial.X 1) = tInv K := by
  simp [alphaPoly, evalVals]

theorem alpha_comp_mk (K : Type) [Field K] :
    (alpha K).comp (Ideal.Quotient.mk (S2801E37Ideal K)) = alphaPoly K :=
  RingHom.ext (fun p => rfl)

theorem S2853PolyHom_X0 (K : Type) [Field K] :
    S2853PolyHom K (MvPolynomial.X 0) = S2801E37X K := by
  simp [S2853PolyHom, S2853Subst, S2801E37X]

theorem S2853PolyHom_X1 (K : Type) [Field K] :
    S2853PolyHom K (MvPolynomial.X 1) = -(S2801E37Y K) - 1 := by
  simp [S2853PolyHom, S2853Subst, S2801E37Y, map_sub, map_neg, map_one]

theorem S2853RingHom_comp_mk (K : Type) [Field K] [DecidableEq K] :
    (S2853RingHom K).comp (Ideal.Quotient.mk (S2801E37Ideal K)) = S2853PolyHom K :=
  RingHom.ext (fun p => rfl)

theorem alpha_comp_S2853PolyHom (K : Type) [Field K] :
    (alpha K).comp (S2853PolyHom K) =
      (alphaPoly K).comp (MvPolynomial.eval₂Hom MvPolynomial.C (S2853Subst K)) := by
  rw [show S2853PolyHom K =
    (Ideal.Quotient.mk (S2801E37Ideal K)).comp
      (MvPolynomial.eval₂Hom MvPolynomial.C (S2853Subst K)) from rfl]
  rw [← RingHom.comp_assoc, alpha_comp_mk]

theorem evalSubst_X0 (K : Type) [Field K] :
    MvPolynomial.eval₂Hom MvPolynomial.C (S2853Subst K) (MvPolynomial.X 0) =
      MvPolynomial.X 0 := by
  rw [MvPolynomial.eval₂Hom_X']
  rfl

theorem evalSubst_X1 (K : Type) [Field K] :
    MvPolynomial.eval₂Hom MvPolynomial.C (S2853Subst K) (MvPolynomial.X 1) =
      -MvPolynomial.X 1 - 1 := by
  rw [MvPolynomial.eval₂Hom_X']
  rfl

theorem evalSubst_C (K : Type) [Field K] (a : K) :
    MvPolynomial.eval₂Hom MvPolynomial.C (S2853Subst K) (MvPolynomial.C a) =
      MvPolynomial.C a :=
  MvPolynomial.eval₂Hom_C _ _ a

theorem hZ (K : Type) [Field K] [DecidableEq K] :
    (phiZ K).comp (g1Ring K) =
      (phiZ K).comp ((alpha K).comp (S2853RingHom K)) := by
  have hL : ((phiZ K).comp (g1Ring K)).comp (Ideal.Quotient.mk (S2801E37Ideal K)) =
      (phiZ K).comp (g1Poly K) := by
    apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply]
    rfl
  have hR : ((phiZ K).comp ((alpha K).comp (S2853RingHom K))).comp
        (Ideal.Quotient.mk (S2801E37Ideal K)) =
      (phiZ K).comp ((alphaPoly K).comp
        (MvPolynomial.eval₂Hom MvPolynomial.C (S2853Subst K))) := by
    apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply]
    rfl
  apply Ideal.Quotient.ringHom_ext
  rw [hL, hR]
  apply MvPolynomial.ringHom_ext
  · intro a
    change phiZ K (g1Poly K (MvPolynomial.C a)) =
      phiZ K (alphaPoly K (MvPolynomial.eval₂Hom MvPolynomial.C (S2853Subst K)
        (MvPolynomial.C a)))
    rw [evalSubst_C]
    have hL : g1Poly K (MvPolynomial.C a) = algebraMap K (A1 K) a := by
      simp [g1Poly]
    have hR : alphaPoly K (MvPolynomial.C a) = algebraMap K (A1 K) a := alphaPoly_C K a
    rw [hL, hR, phiZ_algebraMap_K]
  · intro i
    fin_cases i
    · change phiZ K (g1Poly K (MvPolynomial.X 0)) =
        phiZ K (alphaPoly K (MvPolynomial.eval₂Hom MvPolynomial.C (S2853Subst K)
          (MvPolynomial.X 0)))
      rw [evalSubst_X0]
      have hL : g1Poly K (MvPolynomial.X 0) =
          algebraMap (E37ChartYRing K) (A1 K) (sY K) * tInv K := g1Poly_X0' K
      have hR : alphaPoly K (MvPolynomial.X 0) = s1 K * tInv K := alphaPoly_X0 K
      rw [hL, hR, map_mul, map_mul, phiZ_algebraMap, phiZ_s1]
    · change phiZ K (g1Poly K (MvPolynomial.X 1)) =
        phiZ K (alphaPoly K (MvPolynomial.eval₂Hom MvPolynomial.C (S2853Subst K)
          (MvPolynomial.X 1)))
      rw [evalSubst_X1]
      have hL : g1Poly K (MvPolynomial.X 1) = -1 - tInv K := g1Poly_X1' K
      have hR : alphaPoly K (-(MvPolynomial.X 1) - 1) = -tInv K - 1 := by
        simp [alphaPoly, evalVals]
      rw [hL, hR]
      simp only [map_sub, map_neg, map_one]
      ring

#print axioms hY
#print axioms hZ

end LeanFormal.IUT.XiFPaper.S2856HfRingActual
end