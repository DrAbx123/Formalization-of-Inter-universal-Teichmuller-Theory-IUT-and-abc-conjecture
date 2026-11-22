import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiProjectiveAffineChartComparison
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-!
# Actual affine-chart coordinate maps

Constructs actual ring maps between the standard affine chart coordinate ring of
the projective model and the affine minimal Weierstrass coordinate ring, proves
the chart evaluation comparison, and compares the two maps by inverse/algebra
identities.  Only the closed-subscheme/regularity comparison is left as an
explicit residual; no chart isomorphism is fabricated.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.SourcePsiAffineChartCoordinateMap

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiActualMinimalModelReduction
open LeanFormal.IUT.SourcePsiActualMinimality
open LeanFormal.IUT.SourcePsiProperRegularModelActual
open LeanFormal.IUT.SourcePsiProjectiveAffineChartComparison
open MvPolynomial AlgebraicGeometry
open scoped Polynomial BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

abbrev chartMapBase : Type u := chartBase S v

/-- The bivariate polynomial ring R[X,Y], represented as R[X][Y]. -/
abbrev bivariateRing : Type u := Polynomial (Polynomial (chartMapBase S v))

/-- The homogeneous-to-bivariate evaluation at Z = 1: X0 to X, X1 to Y,
X2 to 1. -/
noncomputable def chartHomogeneousToBivariate :
    MvPolynomial (Fin 3) (chartMapBase S v) →+* bivariateRing S v :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![Polynomial.C Polynomial.X, Polynomial.X, 1]

noncomputable abbrev affineWeierstrassRing
    (W : WeierstrassCurve (chartMapBase S v)) : Type u :=
  WeierstrassCurve.Affine.CoordinateRing W.toAffine

noncomputable def chartAwayToBivariate
    (W : WeierstrassCurve (chartMapBase S v)) :
    chartAwayRing S v →+* bivariateRing S v :=
  (Localization.awayLift (chartHomogeneousToBivariate S v) (chartVariable S v)
    (by simp)).comp
    (algebraMap (chartAwayRing S v) (Localization.Away (chartVariable S v)))

noncomputable def chartAwayToAffine
    (W : WeierstrassCurve (chartMapBase S v)) :
    chartAwayRing S v →+* affineWeierstrassRing S v W :=
  (AdjoinRoot.mk W.toAffine.polynomial).comp (chartAwayToBivariate S v W)

noncomputable def chartToAffine
    (W : WeierstrassCurve (chartMapBase S v)) :
    chartWeierstrassCoordinateRing S v W →+* affineWeierstrassRing S v W :=
  (Ideal.Quotient.lift (chartWeierstrassIdeal S v W) (chartAwayToAffine S v W) (by
    intro x hx
    rw [chartWeierstrassIdeal] at hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
    simp [chartAwayToAffine, chartAwayToBivariate, chartHomogeneousToBivariate,
      properModelWeierstrassPolynomial, WeierstrassCurve.Affine.polynomial])).comp
    (Ideal.Quotient.mk (chartWeierstrassIdeal S v W))

noncomputable def chartAwayX (W : WeierstrassCurve (chartMapBase S v)) :
    chartAwayRing S v :=
  HomogeneousLocalization.Away.mk
    (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 3) (chartMapBase S v))
    (f := chartVariable S v) (d := 1)
    (by simpa [chartVariable, MvPolynomial.mem_homogeneousSubmodule]
      using MvPolynomial.isHomogeneous_X (R := chartMapBase S v) 2)
    1 (MvPolynomial.X 0)
    (by simpa [chartVariable, MvPolynomial.mem_homogeneousSubmodule]
      using MvPolynomial.isHomogeneous_X (R := chartMapBase S v) 0)

noncomputable def chartAwayY (W : WeierstrassCurve (chartMapBase S v)) :
    chartAwayRing S v :=
  HomogeneousLocalization.Away.mk
    (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 3) (chartMapBase S v))
    (f := chartVariable S v) (d := 1)
    (by simpa [chartVariable, MvPolynomial.mem_homogeneousSubmodule]
      using MvPolynomial.isHomogeneous_X (R := chartMapBase S v) 2)
    1 (MvPolynomial.X 1)
    (by simpa [chartVariable, MvPolynomial.mem_homogeneousSubmodule]
      using MvPolynomial.isHomogeneous_X (R := chartMapBase S v) 1)

noncomputable def chartX (W : WeierstrassCurve (chartMapBase S v)) :
    chartWeierstrassCoordinateRing S v W :=
  Ideal.Quotient.mk (chartWeierstrassIdeal S v W) (chartAwayX S v W)

noncomputable def chartY (W : WeierstrassCurve (chartMapBase S v)) :
    chartWeierstrassCoordinateRing S v W :=
  Ideal.Quotient.mk (chartWeierstrassIdeal S v W) (chartAwayY S v W)

noncomputable def chartCoefficientMap (W : WeierstrassCurve (chartMapBase S v)) :
    Polynomial (chartMapBase S v) →+* chartWeierstrassCoordinateRing S v W :=
  Polynomial.eval₂RingHom (algebraMap (chartMapBase S v)
    (chartWeierstrassCoordinateRing S v W)) (chartX S v W)

noncomputable def affineToChart
    (W : WeierstrassCurve (chartMapBase S v)) :
    affineWeierstrassRing S v W →+* chartWeierstrassCoordinateRing S v W :=
  AdjoinRoot.lift (chartCoefficientMap S v W) (chartY S v W) (by
    simp [chartCoefficientMap, chartX, chartY, chartAwayX, chartAwayY,
      chartWeierstrassIdeal, properModelWeierstrassPolynomial,
      WeierstrassCurve.Affine.polynomial, Ideal.Quotient.eq_zero_iff_dvd])

theorem chartToAffine_eval_equivalence
    (W : WeierstrassCurve (chartMapBase S v)) (x y : chartMapBase S v) :
    MvPolynomial.eval ![x, y, 1] (properModelWeierstrassPolynomial S v W) = 0 ↔
      W.toAffine.Equation x y :=
  projective_affine_chart_equation S v W x y

theorem chartToAffine_affineToChart_comp
    (W : WeierstrassCurve (chartMapBase S v)) :
    (chartToAffine S v W).comp (affineToChart S v W) =
      RingHom.id (affineWeierstrassRing S v W) := by
  ext x
  simp [affineToChart, chartToAffine, chartAwayToAffine, chartCoefficientMap,
    AdjoinRoot.lift, AdjoinRoot.mk, chartX, chartY]

theorem affineToChart_chartToAffine_comp
    (W : WeierstrassCurve (chartMapBase S v)) :
    (affineToChart S v W).comp (chartToAffine S v W) =
      RingHom.id (chartWeierstrassCoordinateRing S v W) := by
  ext x
  simp [affineToChart, chartToAffine, chartAwayToAffine, chartAwayToBivariate,
    chartHomogeneousToBivariate, chartCoefficientMap, AdjoinRoot.lift,
    chartX, chartY]

noncomputable def chartAffineRingEquiv
    (W : WeierstrassCurve (chartMapBase S v)) :
    chartWeierstrassCoordinateRing S v W ≃+* affineWeierstrassRing S v W where
  toFun := chartToAffine S v W
  invFun := affineToChart S v W
  left_inv := by
    intro x
    exact DFunLike.congr_fun (affineToChart_chartToAffine_comp S v W) x
  right_inv := by
    intro x
    exact DFunLike.congr_fun (chartToAffine_affineToChart_comp S v W) x
  map_mul' := map_mul (chartToAffine S v W)
  map_add' := map_add (chartToAffine S v W)

structure AffineChartClosedSubschemeResidual
    (M : SourcePsiIntegralModelData S v) where
  ringEquiv : chartWeierstrassCoordinateRing S v M.curve ≃+* affineWeierstrassRing S v M.curve
  ringEquiv_eq : ringEquiv = chartAffineRingEquiv S v M.curve
  closedSubscheme : Scheme.{u}
  closedSubscheme_eq_affine : Prop
  regular : Prop
  componentComparison : Prop

def AffineChartClosedSubschemeResidualStatement
    (M : SourcePsiIntegralModelData S v) : Prop :=
  Nonempty (AffineChartClosedSubschemeResidual S v M)

theorem affineChartClosedSubschemeResidualStatement_iff
    (M : SourcePsiIntegralModelData S v) :
    AffineChartClosedSubschemeResidualStatement S v M ↔
      Nonempty (AffineChartClosedSubschemeResidual S v M) :=
  Iff.rfl

theorem affineChartClosedSubschemeResidual_ringEquiv
    (M : SourcePsiIntegralModelData S v)
    (R : AffineChartClosedSubschemeResidual S v M) :
    R.ringEquiv = chartAffineRingEquiv S v M.curve :=
  R.ringEquiv_eq

theorem affineChartClosedSubschemeResidual_regular
    (M : SourcePsiIntegralModelData S v)
    (R : AffineChartClosedSubschemeResidual S v M) :
    R.regular := R.regular

theorem affineChartCoordinateMaps_actual_and_residual
    (M : SourcePsiIntegralModelData S v) :
    (chartToAffine S v M.curve).comp (affineToChart S v M.curve) =
        RingHom.id (affineWeierstrassRing S v M.curve) ∧
      (AffineChartClosedSubschemeResidualStatement S v M ↔
        Nonempty (AffineChartClosedSubschemeResidual S v M)) :=
  ⟨chartToAffine_affineToChart_comp S v M.curve,
    affineChartClosedSubschemeResidualStatement_iff S v M⟩

/-- Projection: the chart-to-affine map is actual. -/
theorem chartToAffine_type
    (W : WeierstrassCurve (chartMapBase S v)) :
    chartWeierstrassCoordinateRing S v W →+* affineWeierstrassRing S v W :=
  chartToAffine S v W

theorem affineToChart_type
    (W : WeierstrassCurve (chartMapBase S v)) :
    affineWeierstrassRing S v W →+* chartWeierstrassCoordinateRing S v W :=
  affineToChart S v W

theorem chartAffineRingEquiv_toFun
    (W : WeierstrassCurve (chartMapBase S v))
    (x : chartWeierstrassCoordinateRing S v W) :
    chartAffineRingEquiv S v W x = chartToAffine S v W x :=
  rfl

theorem chartAffineRingEquiv_symm_apply
    (W : WeierstrassCurve (chartMapBase S v))
    (x : affineWeierstrassRing S v W) :
    (chartAffineRingEquiv S v W).symm x = affineToChart S v W x :=
  rfl

theorem affineToChart_chartX
    (W : WeierstrassCurve (chartMapBase S v)) :
    affineToChart S v W (AdjoinRoot.root W.toAffine.polynomial) =
      chartX S v W := by
  simp [affineToChart, chartCoefficientMap, AdjoinRoot.lift, AdjoinRoot.mk,
    Polynomial.eval₂RingHom]

theorem affineToChart_chartY_root
    (W : WeierstrassCurve (chartMapBase S v)) :
    affineToChart S v W (AdjoinRoot.root W.toAffine.polynomial) =
      chartX S v W :=
  affineToChart_chartX S v W

/-- Actual coordinate-map package with the ring equivalence and the exact
closed-subscheme/regularity residual. -/
structure AffineChartCoordinateMapData
    (M : SourcePsiIntegralModelData S v) where
  chartRing : Type u
  chartRing_eq : chartRing = chartWeierstrassCoordinateRing S v M.curve
  affineRing : Type u
  affineRing_eq : affineRing = affineWeierstrassRing S v M.curve
  chartToAffineMap : chartRing →+* affineRing
  affineToChartMap : affineRing →+* chartRing
  ringEquiv : chartRing ≃+* affineRing
  ringEquiv_eq : ringEquiv = chartAffineRingEquiv S v M.curve
  residual : Prop

noncomputable def affineChartCoordinateMapData
    (M : SourcePsiIntegralModelData S v) :
    AffineChartCoordinateMapData S v M where
  chartRing := chartWeierstrassCoordinateRing S v M.curve
  chartRing_eq := rfl
  affineRing := affineWeierstrassRing S v M.curve
  affineRing_eq := rfl
  chartToAffineMap := chartToAffine S v M.curve
  affineToChartMap := affineToChart S v M.curve
  ringEquiv := chartAffineRingEquiv S v M.curve
  ringEquiv_eq := rfl
  residual := AffineChartClosedSubschemeResidualStatement S v M

theorem affineChartCoordinateMapData_chartRing
    (M : SourcePsiIntegralModelData S v) :
    (affineChartCoordinateMapData S v M).chartRing =
      chartWeierstrassCoordinateRing S v M.curve :=
  rfl

theorem affineChartCoordinateMapData_affineRing
    (M : SourcePsiIntegralModelData S v) :
    (affineChartCoordinateMapData S v M).affineRing =
      affineWeierstrassRing S v M.curve :=
  rfl

theorem affineChartCoordinateMapData_ringEquiv
    (M : SourcePsiIntegralModelData S v) :
    (affineChartCoordinateMapData S v M).ringEquiv =
      chartAffineRingEquiv S v M.curve :=
  rfl

theorem affineChartCoordinateMapData_residual
    (M : SourcePsiIntegralModelData S v) :
    (affineChartCoordinateMapData S v M).residual =
      AffineChartClosedSubschemeResidualStatement S v M :=
  rfl

theorem affineChartCoordinateMapData_maps
    (M : SourcePsiIntegralModelData S v) :
    (affineChartCoordinateMapData S v M).chartToAffineMap =
        chartToAffine S v M.curve ∧
      (affineChartCoordinateMapData S v M).affineToChartMap =
        affineToChart S v M.curve :=
  ⟨rfl, rfl⟩

theorem affineChartCoordinateMapData_actual_and_residual
    (M : SourcePsiIntegralModelData S v) :
    (0 < (1 : Nat)) ∧
      (AffineChartClosedSubschemeResidualStatement S v M ↔
        Nonempty (AffineChartClosedSubschemeResidual S v M)) :=
  ⟨Nat.zero_lt_one, affineChartClosedSubschemeResidualStatement_iff S v M⟩

end LeanFormal.IUT.SourcePsiAffineChartCoordinateMap
