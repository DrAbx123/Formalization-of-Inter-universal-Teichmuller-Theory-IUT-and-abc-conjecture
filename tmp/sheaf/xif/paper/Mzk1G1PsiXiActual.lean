import tmp.sheaf.xif.paper.Mzk1GlueMorphismActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineTransitionActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLinePiOverlapActual
import tmp.sheaf.xif.paper.Mzk1G1FermatOverlapActual

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiXiActual
open LeanFormal.IUT.XiFPaper.Mzk1GlueMorphismActual
open LeanFormal.IUT.XiFPaper.Mzk1HullFermatGluingActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLinePiOverlapActual

variable (n : Nat)

/-- The unit of the overlap ring whose underlying element is u0. -/
noncomputable def u0Unit : (Overlap0 n)ˣ where
  val := u0 n
  inv := iu0 n
  val_inv := u0_mul_iu0 n
  inv_val := iu0_mul_u0 n

theorem u0Unit_val : ((u0Unit n : (Overlap0 n)ˣ) : Overlap0 n) = u0 n := rfl

theorem u0Unit_inv_val : (((u0Unit n)⁻¹ : (Overlap0 n)ˣ) : Overlap0 n) = iu0 n := rfl

/-- The core transport identity for the lambda chart. -/
theorem chartInf_transport_core (a : Chart0Ring n) :
    overlapToChart0 n ≫ Spec.map (CommRingCat.ofHom (evalAt (R := Chart0Ring n) a)) =
      Spec.map (CommRingCat.ofHom
        (evalAt (R := Overlap0 n) (algebraMap (Chart0Ring n) (Overlap0 n) a))) := by
  show Spec.map (CommRingCat.ofHom (algebraMap (Chart0Ring n) (Overlap0 n))) ≫
      Spec.map (CommRingCat.ofHom (evalAt (R := Chart0Ring n) a)) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  change (algebraMap (Chart0Ring n) (Overlap0 n)).comp (evalAt (R := Chart0Ring n) a) =
    evalAt (R := Overlap0 n) (algebraMap (Chart0Ring n) (Overlap0 n) a)
  apply Polynomial.ringHom_ext
  · intro r
    show (algebraMap (Chart0Ring n) (Overlap0 n))
        ((evalAt (R := Chart0Ring n) a) (Polynomial.C r)) =
      (evalAt (R := Overlap0 n) (algebraMap (Chart0Ring n) (Overlap0 n) a)) (Polynomial.C r)
    rw [evalAt_C, evalAt_C]
    exact IsScalarTower.algebraMap_apply ℚ (Chart0Ring n) (Overlap0 n) r
  · show (algebraMap (Chart0Ring n) (Overlap0 n))
        ((evalAt (R := Chart0Ring n) a) Polynomial.X) =
      (evalAt (R := Overlap0 n) (algebraMap (Chart0Ring n) (Overlap0 n) a)) Polynomial.X
    rw [evalAt_X, evalAt_X]

/-- The core transport identity for the t chart (through the overlap isomorphism beta). -/
theorem chartInf_transport_core_inf (b : ChartInfRing n) :
    overlapToChartInf n ≫ Spec.map (CommRingCat.ofHom (evalAt (R := ChartInfRing n) b)) =
      Spec.map (CommRingCat.ofHom (evalAt (R := Overlap0 n)
        (beta n (algebraMap (ChartInfRing n) (OverlapInf n) b)))) := by
  show Spec.map (CommRingCat.ofHom (beta n)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ChartInfRing n) (OverlapInf n))) ≫
      Spec.map (CommRingCat.ofHom (evalAt (R := ChartInfRing n) b)) = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  change (beta n).comp ((algebraMap (ChartInfRing n) (OverlapInf n)).comp
      (evalAt (R := ChartInfRing n) b)) =
    evalAt (R := Overlap0 n) (beta n (algebraMap (ChartInfRing n) (OverlapInf n) b))
  apply Polynomial.ringHom_ext
  · intro r
    show beta n ((algebraMap (ChartInfRing n) (OverlapInf n))
        ((evalAt (R := ChartInfRing n) b) (Polynomial.C r))) =
      (evalAt (R := Overlap0 n)
        (beta n (algebraMap (ChartInfRing n) (OverlapInf n) b))) (Polynomial.C r)
    rw [evalAt_C, evalAt_C,
      ← IsScalarTower.algebraMap_apply ℚ (ChartInfRing n) (OverlapInf n) r, beta_rat]
  · show beta n ((algebraMap (ChartInfRing n) (OverlapInf n))
        ((evalAt (R := ChartInfRing n) b) Polynomial.X)) =
      (evalAt (R := Overlap0 n)
        (beta n (algebraMap (ChartInfRing n) (OverlapInf n) b))) Polynomial.X
    rw [evalAt_X, evalAt_X]

/-- Transport of lambda-chart morphisms to the overlap. -/
theorem overlapToChart0_chartMorphismInf (a : Chart0Ring n) :
    overlapToChart0 n ≫ chartMorphismInf (R := Chart0Ring n) a =
      chartMorphismInf (R := Overlap0 n) (algebraMap (Chart0Ring n) (Overlap0 n) a) := by
  rw [chartMorphismInf, chartMorphismInf, ← Category.assoc, chartInf_transport_core]

/-- Transport of t-chart morphisms to the overlap. -/
theorem overlapToChartInf_chartMorphism0 (b : ChartInfRing n) :
    overlapToChartInf n ≫ chartMorphism0 (R := ChartInfRing n) b =
      chartMorphism0 (R := Overlap0 n)
        (beta n (algebraMap (ChartInfRing n) (OverlapInf n) b)) := by
  rw [chartMorphism0, chartMorphism0, ← Category.assoc, chartInf_transport_core_inf]

/-- Glue a morphism out of the two-chart glued Fermat curve from compatible chart
morphisms. -/
noncomputable def fermatCurveGlueMorphism {Z : Scheme}
    (f0 : fermatChart0Scheme n ⟶ Z) (f1 : fermatChartInfScheme n ⟶ Z)
    (h : overlapToChart0 n ≫ f0 = overlapToChartInf n ≫ f1) :
    fermatCurveScheme n ⟶ Z :=
  glueMorphism (D := fermatTwoChartGlueData n)
    (fun i => match i with
      | ULift.up false => f0
      | ULift.up true => f1)
    (by
      rintro ⟨i⟩ ⟨j⟩
      cases i <;> cases j
      · show 𝟙 (fermatChart0Scheme n) ≫ f0 =
          𝟙 (fermatChart0Scheme n) ≫ 𝟙 (fermatChart0Scheme n) ≫ f0
        simp
      · show overlapToChart0 n ≫ f0 = 𝟙 (fermatOverlapScheme n) ≫ overlapToChartInf n ≫ f1
        rw [Category.id_comp]
        exact h
      · show overlapToChartInf n ≫ f1 = 𝟙 (fermatOverlapScheme n) ≫ overlapToChart0 n ≫ f0
        rw [Category.id_comp]
        exact h.symm
      · show 𝟙 (fermatChartInfScheme n) ≫ f1 =
          𝟙 (fermatChartInfScheme n) ≫ 𝟙 (fermatChartInfScheme n) ≫ f1
        simp)

/-- The x-coordinate morphism Y_n -> P^1: t-chart value x on the first chart and
lambda-chart value r = 1/x on the chart at infinity. -/
noncomputable def xi :
    fermatCurveScheme n ⟶ Mzk1G1ProjectiveLineGluedActual.projectiveLineGlued :=
  fermatCurveGlueMorphism n
    (chartMorphismInf (R := Chart0Ring n) (x0 n))
    (chartMorphism0 (R := ChartInfRing n) (r1 n))
    (by
      rw [overlapToChart0_chartMorphismInf, overlapToChartInf_chartMorphism0]
      rw [show (algebraMap (ChartInfRing n) (OverlapInf n)) (r1 n) = u1 n from rfl, beta_u1]
      show chartMorphismInf (R := Overlap0 n) (u0 n) =
        chartMorphism0 (R := Overlap0 n) (iu0 n)
      exact (chartMorphism_transition (R := Overlap0 n) (u0Unit n)⁻¹).symm)

#print axioms chartInf_transport_core
#print axioms chartInf_transport_core_inf
#print axioms overlapToChart0_chartMorphismInf
#print axioms overlapToChartInf_chartMorphism0
#print axioms fermatCurveGlueMorphism
#print axioms xi
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiXiActual
