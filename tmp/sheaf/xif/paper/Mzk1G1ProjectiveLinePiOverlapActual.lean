import tmp.sheaf.xif.paper.Mzk1G1FermatOverlapActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineTransitionActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLinePiOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual

variable (n : Nat)

/-- beta fixes the rational scalars. -/
theorem beta_rat (a : ℚ) :
    beta n (algebraMap ℚ (OverlapInf n) a) = algebraMap ℚ (Overlap0 n) a := by
  have h1 : algebraMap ℚ (OverlapInf n) a =
      algebraMap (ChartInfRing n) (OverlapInf n) (algebraMap ℚ (ChartInfRing n) a) :=
    (IsScalarTower.algebraMap_apply ℚ (ChartInfRing n) (OverlapInf n) a).symm
  rw [h1, beta_algebraMap]
  have h2 : algebraMap ℚ (ChartInfRing n) a =
      Ideal.Quotient.mk (idealInf n) (MvPolynomial.C a) :=
    algebraMap_rat_chartInf n a
  rw [h2, phi_mk, phiAux_def, MvPolynomial.eval₂Hom_C]
  exact IsScalarTower.algebraMap_apply ℚ (Chart0Ring n) (Overlap0 n) a

/-- The overlap inclusion into the first chart in coordinates: the point u0 is the image
of the point x0. -/
theorem overlapToChart0_spec :
    (overlapToChart0 n) ≫
        Spec.map (CommRingCat.ofHom (evalAt (R := Chart0Ring n) (x0 n ^ n))) =
      Spec.map (CommRingCat.ofHom (evalAt (R := Overlap0 n) (u0 n ^ n))) := by
  show Spec.map (CommRingCat.ofHom (algebraMap (Chart0Ring n) (Overlap0 n))) ≫
      Spec.map (CommRingCat.ofHom (evalAt (R := Chart0Ring n) (x0 n ^ n))) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply Polynomial.ringHom_ext
  · intro r
    show (algebraMap (Chart0Ring n) (Overlap0 n))
      ((evalAt (R := Chart0Ring n) (x0 n ^ n)) (Polynomial.C r)) =
        (evalAt (R := Overlap0 n) (u0 n ^ n)) (Polynomial.C r)
    rw [evalAt_C, evalAt_C]
    rw [IsScalarTower.algebraMap_apply ℚ (Chart0Ring n) (Overlap0 n) r]
  · show (algebraMap (Chart0Ring n) (Overlap0 n))
      ((evalAt (R := Chart0Ring n) (x0 n ^ n)) Polynomial.X) =
        (evalAt (R := Overlap0 n) (u0 n ^ n)) Polynomial.X
    rw [evalAt_X, evalAt_X]
    rw [map_pow, show (algebraMap (Chart0Ring n) (Overlap0 n)) (x0 n) = u0 n from rfl]

/-- The overlap inclusion into the second chart in coordinates: the image of r1^n is
iu0^n, the inverse of u0^n. -/
theorem overlapToChartInf_spec :
    (overlapToChartInf n) ≫
        Spec.map (CommRingCat.ofHom (evalAt (R := ChartInfRing n) (r1 n ^ n))) =
      Spec.map (CommRingCat.ofHom (evalAt (R := Overlap0 n) (iu0 n ^ n))) := by
  have hring : (beta n).comp ((algebraMap (ChartInfRing n) (OverlapInf n)).comp
      (evalAt (R := ChartInfRing n) (r1 n ^ n))) =
      (evalAt (R := Overlap0 n) (iu0 n ^ n)) := by
    apply Polynomial.ringHom_ext
    · intro r
      show beta n (algebraMap (ChartInfRing n) (OverlapInf n)
        ((evalAt (R := ChartInfRing n) (r1 n ^ n)) (Polynomial.C r))) =
          (evalAt (R := Overlap0 n) (iu0 n ^ n)) (Polynomial.C r)
      rw [evalAt_C, evalAt_C]
      rw [← IsScalarTower.algebraMap_apply ℚ (ChartInfRing n) (OverlapInf n) r]
      rw [beta_rat]
    · show beta n (algebraMap (ChartInfRing n) (OverlapInf n)
        ((evalAt (R := ChartInfRing n) (r1 n ^ n)) Polynomial.X)) =
          (evalAt (R := Overlap0 n) (iu0 n ^ n)) Polynomial.X
      rw [evalAt_X, evalAt_X]
      rw [map_pow, map_pow]
      rw [show (algebraMap (ChartInfRing n) (OverlapInf n)) (r1 n) = u1 n from rfl]
      rw [beta_u1]
  show Spec.map (CommRingCat.ofHom (beta n)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ChartInfRing n) (OverlapInf n))) ≫
      Spec.map (CommRingCat.ofHom (evalAt (R := ChartInfRing n) (r1 n ^ n))) = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rw [show (CommRingCat.ofHom (evalAt (R := ChartInfRing n) (r1 n ^ n)) ≫
      CommRingCat.ofHom (algebraMap (ChartInfRing n) (OverlapInf n))) ≫
      CommRingCat.ofHom (beta n) =
      CommRingCat.ofHom (evalAt (R := Overlap0 n) (iu0 n ^ n)) from by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom hring]

/-- The unit of the overlap ring whose underlying element is u0^n. -/
noncomputable def overlapUnit : (Overlap0 n)ˣ where
  val := u0 n ^ n
  inv := iu0 n ^ n
  val_inv := by rw [← mul_pow, u0_mul_iu0, one_pow]
  inv_val := by rw [← mul_pow, iu0_mul_u0, one_pow]

theorem overlapUnit_val : ((overlapUnit n : (Overlap0 n)ˣ) : Overlap0 n) = u0 n ^ n := rfl

theorem overlapUnit_inv_val : (((overlapUnit n)⁻¹ : (Overlap0 n)ˣ) : Overlap0 n) = iu0 n ^ n :=
  rfl

/-- THE pi-OVERLAP COMPATIBILITY: the two chart restrictions of the projection
pi : Y_n -> P^1 agree on the overlap D(x) = D(r) (the transition t = lambda^{-1}). -/
theorem fermatPiOverlap_condition :
    overlapToChart0 n ≫ chartMorphism0 (R := Chart0Ring n) (x0 n ^ n) =
      overlapToChartInf n ≫ chartMorphismInf (R := ChartInfRing n) (r1 n ^ n) := by
  rw [chartMorphism0, chartMorphismInf]
  rw [← Category.assoc, ← Category.assoc]
  rw [overlapToChart0_spec, overlapToChartInf_spec]
  exact chartMorphism_transition (R := Overlap0 n) (overlapUnit n)

#print axioms fermatPiOverlap_condition
end LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLinePiOverlapActual
