import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineGluedActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineTransitionActual
import Mathlib.Tactic

/-!
# route §4.4 (L321-325): the scheme-level morphism hPoly : P^1 -> P^1 for a polynomial h

On the canonical glued P^1 (chart0 coordinate lambda, chartInf coordinate t = 1/lambda)
the two quotient functions of the route become THREE chart pieces (approved M-A):
  piece 0: chartInf, t-coordinate h(t)
  piece 1: D(lambda) inside chart0, t-coordinate lambda^{-d} * hRev(lambda)
  piece 2: D(hRev) inside chart0, lambda-coordinate lambda^d / hRev(lambda)
where hRev is the reverse polynomial, with hRev(0) = leading coefficient of h.
The cover of the lambda-chart by D(lambda) and D(hRev) holds since (lambda, hRev) = top.

Intersection D(lambda * hRev): the two coordinates are
  t = hRev^(d+1) * (lambda * hRev)^{-d},  lambda = lambda^(d+1) * (lambda * hRev)^{-1},
whose product is 1 (the unit needed for the chart transition).
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual

variable (h : Polynomial ℚ)

/-- The reverse polynomial hRev = lambda^d * h(1/lambda); its value at 0 is the leading
coefficient of h. -/
noncomputable def hRev : Polynomial ℚ :=
  ∑ i ∈ h.support, Polynomial.C (h.coeff i) * Polynomial.X ^ (h.natDegree - i)

/-- The t-coordinate of hPoly on the D(lambda) piece: lambda^{-d} * hRev(lambda). -/
noncomputable def hPolyT :
    Localization.Away (Polynomial.X : Polynomial ℚ) :=
  (IsLocalization.Away.invSelf (x := (Polynomial.X : Polynomial ℚ))) ^ h.natDegree *
    algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ)) (hRev h)

/-- The lambda-coordinate of hPoly on the D(hRev) piece: lambda^d / hRev(lambda). -/
noncomputable def hPolyLam : Localization.Away (hRev h) :=
  (algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) Polynomial.X) ^ h.natDegree *
    IsLocalization.Away.invSelf (x := hRev h)

/-- Cover piece 0: the t-chart of P^1. -/
noncomputable def hPolyPiece0 : Spec (CommRingCat.of (Polynomial ℚ)) ⟶ projectiveLineGlued :=
  localChartInf

/-- Cover piece 1: D(lambda) inside the lambda-chart. -/
noncomputable def hPolyPiece1 :
    Spec (CommRingCat.of (Localization.Away (Polynomial.X : Polynomial ℚ))) ⟶
      projectiveLineGlued :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ)))) ≫
    localChart0

/-- Cover piece 2: D(hRev) inside the lambda-chart. -/
noncomputable def hPolyPiece2 :
    Spec (CommRingCat.of (Localization.Away (hRev h))) ⟶ projectiveLineGlued :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ) (Localization.Away (hRev h)))) ≫
    localChart0

/-- The chart morphism of hPoly on piece 0: t-coordinate h(t). -/
noncomputable def hPolyChart0 :
    Spec (CommRingCat.of (Polynomial ℚ)) ⟶ projectiveLineGlued :=
  chartMorphismInf (R := Polynomial ℚ) h

/-- The chart morphism of hPoly on piece 1: t-coordinate lambda^{-d} hRev(lambda). -/
noncomputable def hPolyChart1 : Spec (CommRingCat.of
      (Localization.Away (Polynomial.X : Polynomial ℚ))) ⟶ projectiveLineGlued :=
  chartMorphismInf (R := Localization.Away (Polynomial.X : Polynomial ℚ)) (hPolyT h)

/-- The chart morphism of hPoly on piece 2: lambda-coordinate lambda^d / hRev(lambda). -/
noncomputable def hPolyChart2 : Spec (CommRingCat.of (Localization.Away (hRev h))) ⟶
    projectiveLineGlued :=
  chartMorphism0 (R := Localization.Away (hRev h)) (hPolyLam h)

/-- The intersection D(lambda * hRev) of pieces 1 and 2, as a scheme. -/
noncomputable abbrev hPolyIntersection : Scheme :=
  Spec (CommRingCat.of (Localization.Away
    (Polynomial.X * hRev h : Polynomial ℚ)))

/-- Its inclusion into P^1 through the lambda chart. -/
noncomputable def hPolyIntersectionToP1 : hPolyIntersection h ⟶ projectiveLineGlued :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ)
    (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)))) ≫ localChart0

/-- The lambda-coordinate on the intersection: lambda^(d+1) * (lambda*hRev)^{-1}. -/
noncomputable def hPolyLamOnIntersection :
    Localization.Away (Polynomial.X * hRev h : Polynomial ℚ) :=
  (algebraMap (Polynomial ℚ)
      (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) Polynomial.X) ^
        (h.natDegree + 1) *
    IsLocalization.Away.invSelf
      (x := (Polynomial.X * hRev h : Polynomial ℚ))

/-- The t-coordinate on the intersection: hRev^(d+1) * (lambda*hRev)^{-d}. -/
noncomputable def hPolyTOnIntersection :
    Localization.Away (Polynomial.X * hRev h : Polynomial ℚ) :=
  (algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))
      (hRev h)) ^ (h.natDegree + 1) *
    IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ)) ^ h.natDegree

/-!
## HANDOFF (next writer: henry, per Lead): hPoly ③ (unit group recipe, no set/calc)

Goal: hPolyOnIntersection_mul : hPolyLamOnIntersection h * hPolyTOnIntersection h = 1.

Step 1 (units of the intersection ring), in Localization.Away (X * hRev h):
  theorem isUnit_intersection_X : IsUnit (algebraMap _ _ Polynomial.X)
  theorem isUnit_intersection_hRev : IsUnit (algebraMap _ _ (hRev h))
Both by isUnit_of_dvd_unit: the product algebraMap (X * hRev h) is a unit
(IsLocalization.Away.algebraMap_isUnit), rewrite map_mul at it, then
isUnit_of_dvd_unit (dvd_mul_right _ _) hprod for X and
isUnit_of_dvd_unit (dvd_mul_left _ _) hprod for hRev.
Define uX := (isUnit_intersection_X h).unit, uH := (isUnit_intersection_hRev h).unit,
uC := uX * uH with Units.val_mul + map_mul giving val uC = algebraMap (X * hRev h).

Step 2 (coordinates as unit values). Let S := IsLocalization.Away.invSelf (x := X * hRev h)
(so algebraMap (X*hRev) * S = 1 by IsLocalization.Away.mul_invSelf, and
val (uC⁻¹) = S by cancelling the common left factor algebraMap (X*hRev) in
algebraMap (X*hRev) * S = 1 and Units.mul_inv). Then
hPolyLamOnIntersection h = val (uX ^ (d+1) * uC⁻¹) and
hPolyTOnIntersection h = val (uH ^ (d+1) * (uC⁻¹) ^ d)
(rewrite with Units.val_pow/Units.val_mul, mul_pow, map_mul).

Step 3 (product). Multiply:
val (uX^(d+1) * uC⁻¹ * uH^(d+1) * (uC⁻¹)^d) = val (uX^(d+1) * uH^(d+1) * (uC^(d+1))⁻¹)
(commutativity in the unit group, pow_succ, inv_pow), then
uX^(d+1) * uH^(d+1) = uC^(d+1) (by mul_pow), so the value is
val (uC^(d+1) * (uC^(d+1))⁻¹) = val 1 = 1 by Units.mul_inv and Units.val_one.

Step 4. hPolyUnit (val = hPolyLamOnIntersection h, inv = hPolyTOnIntersection h, fields from
hPolyOnIntersection_mul and its mul_comm variant), then
hPoly_overlap_compat : chartMorphismInf (R := Away (X * hRev h)) (hPolyTOnIntersection h) =
  chartMorphism0 (R := Away (X * hRev h)) (hPolyLamOnIntersection h)
by (chartMorphism_transition (R := Away (X * hRev h)) (hPolyUnit h)).symm plus a show to align
val (u⁻¹) with hPolyTOnIntersection h (definitionally rfl by the unit fields).

Then: coverage (localChart_jointly_surjective + chart0 = D(lambda) ∪ D(hRev) from
(lambda, hRev) = top, itself from (hRev h).coeff 0 = h.leadingCoeff ≠ 0 giving
C h_d ∈ Ideal.span {X, hRev}), the 3-piece OpenCover, glueMorphisms, and
hPoly/hPoly_ι0/ι1/ι2.  NOTE: route L321-325; M-A approved by Lead.
-/

/-! ## hPoly ③: the unit group recipe (HANDOFF steps 1-4). -/
/-- The product `lambda * hRev` is a unit in the intersection ring. -/
theorem isUnit_intersection_mul (h : Polynomial ℚ) :
    IsUnit (algebraMap (Polynomial ℚ)
      (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))
      (Polynomial.X * hRev h)) :=
  IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))
    (x := Polynomial.X * hRev h)
/-- `lambda` is a unit in the intersection ring. -/
theorem isUnit_intersection_X (h : Polynomial ℚ) :
    IsUnit (algebraMap (Polynomial ℚ)
      (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) Polynomial.X) := by
  have hprod := isUnit_intersection_mul h
  rw [map_mul] at hprod
  exact isUnit_of_dvd_unit (dvd_mul_right _ _) hprod
/-- `hRev` is a unit in the intersection ring. -/
theorem isUnit_intersection_hRev (h : Polynomial ℚ) :
    IsUnit (algebraMap (Polynomial ℚ)
      (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) (hRev h)) := by
  have hprod := isUnit_intersection_mul h
  rw [map_mul] at hprod
  exact isUnit_of_dvd_unit (dvd_mul_left _ _) hprod
/-- The unit `uX` with value `lambda`. -/
noncomputable def uX (h : Polynomial ℚ) :
    (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ :=
  (isUnit_intersection_X h).unit
/-- The unit `uH` with value `hRev`. -/
noncomputable def uH (h : Polynomial ℚ) :
    (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ :=
  (isUnit_intersection_hRev h).unit
/-- The unit `uC = uX * uH`, with value `lambda * hRev`. -/
noncomputable def uC (h : Polynomial ℚ) :
    (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ :=
  uX h * uH h
theorem uX_val (h : Polynomial ℚ) :
    ((uX h : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) :
      Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) =
      algebraMap (Polynomial ℚ)
        (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) Polynomial.X :=
  IsUnit.unit_spec _
theorem uH_val (h : Polynomial ℚ) :
    ((uH h : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) :
      Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) =
      algebraMap (Polynomial ℚ)
        (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) (hRev h) :=
  IsUnit.unit_spec _
theorem uC_val (h : Polynomial ℚ) :
    ((uC h : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) :
      Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) =
      algebraMap (Polynomial ℚ)
        (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))
        (Polynomial.X * hRev h) := by
  rw [uC, Units.val_mul, uX_val, uH_val, map_mul]
theorem invSelf_eq_inv_uC (h : Polynomial ℚ) :
    IsLocalization.Away.invSelf
        (x := (Polynomial.X * hRev h : Polynomial ℚ)) =
      (((uC h)⁻¹ : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) :
        Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) := by
  have hmul : ((uC h : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) :
        Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) *
      IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ)) = 1 := by
    rw [uC_val, IsLocalization.Away.mul_invSelf]
  have hcancel : ((uC h : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) :
      Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) *
      IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ)) = 1 := hmul
  calc IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ))
      = 1 * IsLocalization.Away.invSelf
          (x := (Polynomial.X * hRev h : Polynomial ℚ)) := (one_mul _).symm
    _ = ((((uC h)⁻¹ * uC h : (Localization.Away
            (Polynomial.X * hRev h : Polynomial ℚ))ˣ) :
        Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))) *
        IsLocalization.Away.invSelf
          (x := (Polynomial.X * hRev h : Polynomial ℚ)) := by
          rw [inv_mul_cancel, Units.val_one]
    _ = (((uC h)⁻¹ : (Localization.Away
            (Polynomial.X * hRev h : Polynomial ℚ))ˣ) :
        Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) *
        (((uC h : (Localization.Away
            (Polynomial.X * hRev h : Polynomial ℚ))ˣ) :
          Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) *
          IsLocalization.Away.invSelf
            (x := (Polynomial.X * hRev h : Polynomial ℚ))) := by
          rw [Units.val_mul, mul_assoc]
    _ = (((uC h)⁻¹ : (Localization.Away
            (Polynomial.X * hRev h : Polynomial ℚ))ˣ) :
        Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) := by
          rw [hcancel, mul_one]
/-! Step 2: the intersection coordinates are unit values. -/
theorem hPolyLamOnIntersection_eq (h : Polynomial ℚ) :
    hPolyLamOnIntersection h =
      ((((uX h) ^ (h.natDegree + 1) * (uC h)⁻¹ :
          (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) : Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))) := by
  show (algebraMap (Polynomial ℚ)
        (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) Polynomial.X) ^
      (h.natDegree + 1) *
      IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ)) = _
  rw [invSelf_eq_inv_uC, Units.val_mul, Units.val_pow_eq_pow_val, uX_val]
theorem hPolyTOnIntersection_eq (h : Polynomial ℚ) :
    hPolyTOnIntersection h =
      ((((uH h) ^ (h.natDegree + 1) * ((uC h)⁻¹) ^ h.natDegree :
          (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) : Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))) := by
  show (algebraMap (Polynomial ℚ)
        (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) (hRev h)) ^
      (h.natDegree + 1) *
      IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ)) ^
        h.natDegree = _
  rw [invSelf_eq_inv_uC, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, uH_val]
/-! Step 3: the product of the two intersection coordinates is 1. -/
theorem hPolyOnIntersection_mul (h : Polynomial ℚ) :
    hPolyLamOnIntersection h * hPolyTOnIntersection h = 1 := by
  rw [hPolyLamOnIntersection_eq h, hPolyTOnIntersection_eq h, ← Units.val_mul]
  have hunit : ((uX h) ^ (h.natDegree + 1) * (uC h)⁻¹ *
      ((uH h) ^ (h.natDegree + 1) * ((uC h)⁻¹) ^ h.natDegree) :
      (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) = 1 := by
    refine Units.ext ?_
    have h1 : ((uX h : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) : Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) ^ (h.natDegree + 1) *
        IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ)) *
        (((uH h : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) : Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) ^ (h.natDegree + 1) *
          IsLocalization.Away.invSelf
            (x := (Polynomial.X * hRev h : Polynomial ℚ)) ^ h.natDegree) = 1 := by
      have hab : ((uX h : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) : Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) *
          ((uH h : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) : Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) =
          algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) (Polynomial.X * hRev h) := by
        rw [uX_val, uH_val, ← map_mul]
      have hS : ((uX h : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) : Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) *
          ((uH h : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) : Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) *
          IsLocalization.Away.invSelf
            (x := (Polynomial.X * hRev h : Polynomial ℚ)) = 1 := by
        rw [hab, IsLocalization.Away.mul_invSelf]
      calc ((uX h : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) : Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) ^ (h.natDegree + 1) *
            IsLocalization.Away.invSelf (x := (Polynomial.X * hRev h : Polynomial ℚ)) *
            (((uH h : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) : Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) ^ (h.natDegree + 1) *
              IsLocalization.Away.invSelf
                (x := (Polynomial.X * hRev h : Polynomial ℚ)) ^ h.natDegree)
          = ((((uX h : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) : Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) *
              ((uH h : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) : Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))) ^ (h.natDegree + 1) *
              IsLocalization.Away.invSelf
                (x := (Polynomial.X * hRev h : Polynomial ℚ)) ^ (h.natDegree + 1)) := by
            ring
        _ = ((((uX h : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) : Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) *
              ((uH h : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) : Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) *
              IsLocalization.Away.invSelf
                (x := (Polynomial.X * hRev h : Polynomial ℚ))) ^ (h.natDegree + 1)) := by
            simp only [mul_pow]
        _ = 1 := by rw [hS, one_pow]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one,
      ← Units.val_inv_eq_inv_val, ← invSelf_eq_inv_uC, uX_val, uH_val]
    exact h1
  rw [hunit]
  rfl
/-! Step 4: the overlap transition. -/
noncomputable def hPolyUnit (h : Polynomial ℚ) :
    (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ where
  val := hPolyLamOnIntersection h
  inv := hPolyTOnIntersection h
  val_inv := hPolyOnIntersection_mul h
  inv_val := (mul_comm _ _).trans (hPolyOnIntersection_mul h)
theorem hPoly_overlap_compat (h : Polynomial ℚ) :
    chartMorphismInf (R := Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))
        (hPolyTOnIntersection h) =
      chartMorphism0 (R := Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))
        (hPolyLamOnIntersection h) := by
  have htrans : chartMorphism0 (R := Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) ((hPolyUnit h : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) : Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) =
      chartMorphismInf (R := Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) ((((hPolyUnit h)⁻¹ : (Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))ˣ) : Localization.Away (Polynomial.X * hRev h : Polynomial ℚ))) :=
    chartMorphism_transition (R := Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) (hPolyUnit h)
  rw [show ((hPolyUnit h : (Localization.Away
      (Polynomial.X * hRev h : Polynomial ℚ))ˣ) :
      Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) =
      hPolyLamOnIntersection h from rfl,
    show (((hPolyUnit h)⁻¹ : (Localization.Away
      (Polynomial.X * hRev h : Polynomial ℚ))ˣ) :
      Localization.Away (Polynomial.X * hRev h : Polynomial ℚ)) =
      hPolyTOnIntersection h from rfl] at htrans
  exact htrans.symm
#print axioms hRev
#print axioms hPolyT
#print axioms hPolyLam
#print axioms hPolyPiece0
#print axioms hPolyPiece1
#print axioms hPolyPiece2
#print axioms hPolyChart0
#print axioms hPolyChart1
#print axioms hPolyChart2
#print axioms hPolyIntersectionToP1
#print axioms hPolyLamOnIntersection
#print axioms hPolyTOnIntersection
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual

-- t-- t2
