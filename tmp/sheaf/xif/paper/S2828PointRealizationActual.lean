import tmp.sheaf.xif.paper.S2822PointRealizationRouteActual
import Mathlib.AlgebraicGeometry.OpenImmersion
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S2828PointRealizationActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2822PointRealizationRouteActual
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
universe u
variable (F : Type u) [Field F]

/-- S2828 step 1: an F-point of the glued E37 scheme factors through chart Z
or chart Y. The F-point's image is a single point (`Spec F` is a subsingleton),
so the actual point-cover lemma applies and the open-immersion lift gives the
factorization. -/
theorem S2828_fpoint_factors_chart
    (e : E37ChartZOverlap F ≅ E37ChartYOverlap F)
    (x : Spec (CommRingCat.of F) ⟶ E37ProjGluedScheme F e) :
    (∃ z : Spec (CommRingCat.of F) ⟶ S2801E37AffineScheme F,
        z ≫ E37ProjChartZMap F e = x) ∨
      (∃ y : Spec (CommRingCat.of F) ⟶ E37ChartYScheme F,
        y ≫ E37ProjChartYMap F e = x) := by
  haveI : Subsingleton (Spec (CommRingCat.of F)) := inferInstance
  haveI hZ : IsOpenImmersion (E37ProjChartZMap F e) :=
    (E37ProjGlueData F e).ι_isOpenImmersion (ULift.up false)
  haveI hY : IsOpenImmersion (E37ProjChartYMap F e) :=
    (E37ProjGlueData F e).ι_isOpenImmersion (ULift.up true)
  let p : Spec (CommRingCat.of F) := default
  have hp : ∀ q : Spec (CommRingCat.of F), q = p := fun q => Subsingleton.elim q p
  rcases S2822_E37ProjCharts_jointly_surjective F e (x p) with ⟨z, hz⟩ | ⟨y, hy⟩
  · left
    refine ⟨IsOpenImmersion.lift (E37ProjChartZMap F e) x ?_,
      IsOpenImmersion.lift_fac (E37ProjChartZMap F e) x ?_⟩
    · rintro q ⟨r, rfl⟩
      exact ⟨z, by rw [hp r]; exact hz⟩
    · rintro q ⟨r, rfl⟩
      exact ⟨z, by rw [hp r]; exact hz⟩
  · right
    refine ⟨IsOpenImmersion.lift (E37ProjChartYMap F e) x ?_,
      IsOpenImmersion.lift_fac (E37ProjChartYMap F e) x ?_⟩
    · rintro q ⟨r, rfl⟩
      exact ⟨y, by rw [hp r]; exact hy⟩
    · rintro q ⟨r, rfl⟩
      exact ⟨y, by rw [hp r]; exact hy⟩

/-- S2828 step 2a: extract the coordinate-ring F-point from an affine-scheme
F-point. -/
noncomputable def S2828_chartZHom
    (x : Spec (CommRingCat.of F) ⟶ S2801E37AffineScheme F) :
    S2801E37CoordinateRing F →+* F :=
  (Spec.homEquiv (R := CommRingCat.of (S2801E37CoordinateRing F))
    (S := CommRingCat.of F) x).hom

/-- S2828 step 2b: the extracted coordinates satisfy the E37 affine equation,
directly from `S2801E37_relation`. -/
theorem S2828_chartZ_equation
    (x : Spec (CommRingCat.of F) ⟶ S2801E37AffineScheme F) :
    (S2801E37Curve F).toAffine.Equation
      (S2828_chartZHom F x (S2801E37X F))
      (S2828_chartZHom F x (S2801E37Y F)) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have h := congrArg (S2828_chartZHom F x) (S2801E37_relation F)
  simpa [S2801E37Curve, sub_eq_add_neg] using h

#print axioms S2828_fpoint_factors_chart
#print axioms S2828_chartZ_equation
end LeanFormal.IUT.XiFPaper.S2828PointRealizationActual
end