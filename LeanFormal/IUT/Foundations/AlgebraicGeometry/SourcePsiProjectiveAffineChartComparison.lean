import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiProperRegularModelActual
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Tactic

/-! # Affine chart Z = 1 comparison for the actual projective model -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.SourcePsiProjectiveAffineChartComparison

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiActualMinimalModelReduction
open LeanFormal.IUT.SourcePsiActualMinimality
open LeanFormal.IUT.SourcePsiProperRegularModelActual
open MvPolynomial AlgebraicGeometry
open scoped Polynomial BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

abbrev chartBase : Type u := properModelBase S v
abbrev chartHomogeneousRing : Type u := properModelHomogeneousRing (chartBase S v)

noncomputable def chartVariable : chartHomogeneousRing S v := MvPolynomial.X 2

noncomputable def projectiveAffineChartOpen : (properModelProjectiveSpace S v).Opens :=
  AlgebraicGeometry.Proj.basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin 3) (chartBase S v)) (chartVariable S v)

abbrev chartAwayRing : Type u :=
  HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 3)
    (chartBase S v)) (chartVariable S v)

abbrev chartWeierstrassCoordinateRing (W : WeierstrassCurve (chartBase S v)) : Type u :=
  chartAwayRing S v ⧸ Ideal.span {properModelWeierstrassPolynomial S v W}

noncomputable abbrev affineMinimalChart (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve.Affine (chartBase S v) := properModelAffineChart S v M

noncomputable abbrev affineMinimalCoordinateRing
    (M : SourcePsiIntegralModelData S v) : Type u := properModelAffineCoordinateRing S v M

theorem projective_affine_chart_equation
    (W : WeierstrassCurve (chartBase S v)) (x y : chartBase S v) :
    MvPolynomial.eval ![x, y, 1] (properModelWeierstrassPolynomial S v W) = 0 ↔
      W.toAffine.Equation x y :=
  by
  simp [properModelWeierstrassPolynomial, WeierstrassCurve.Affine.Equation,
    WeierstrassCurve.Affine.polynomial, MvPolynomial.eval]

def AffineChartEquationComparison : Prop :=
  ∀ (W : WeierstrassCurve (chartBase S v)) (x y : chartBase S v),
    MvPolynomial.eval ![x, y, 1] (properModelWeierstrassPolynomial S v W) = 0 ↔
      W.toAffine.Equation x y

theorem affineChartEquationComparison_holds : AffineChartEquationComparison S v :=
  fun W x y => projective_affine_chart_equation S v W x y

noncomputable def projectiveAffineChartOpenImmersion :
    projectiveAffineChartOpen S v ⟶ properModelProjectiveSpace S v :=
  (projectiveAffineChartOpen S v).ι

theorem projectiveAffineChartOpen_isOpen :
    IsOpenImmersion (projectiveAffineChartOpenImmersion S v) :=
  (projectiveAffineChartOpen S v).ι_isOpenImmersion

noncomputable def projectiveAffineChartToSpec :
    projectiveAffineChartOpen S v ⟶ Spec (CommRingCat.of (chartAwayRing S v)) :=
  AlgebraicGeometry.Proj.basicOpenToSpec
    (MvPolynomial.homogeneousSubmodule (Fin 3) (chartBase S v)) (chartVariable S v)

structure AffineChartCoordinateComparisonResidual
    (M : SourcePsiIntegralModelData S v) where
  affineRing : Type u
  affineRing_eq : affineRing = affineMinimalCoordinateRing S v M
  chartRing : Type u
  chartRing_eq : chartRing = chartWeierstrassCoordinateRing S v M.curve
  affineToChart : Prop
  chartToAffine : Prop
  left_inverse : Prop
  right_inverse : Prop

def AffineChartCoordinateComparisonStatement (M : SourcePsiIntegralModelData S v) : Prop :=
  Nonempty (AffineChartCoordinateComparisonResidual S v M)

theorem affineChartCoordinateComparisonStatement_iff
    (M : SourcePsiIntegralModelData S v) :
    AffineChartCoordinateComparisonStatement S v M ↔
      Nonempty (AffineChartCoordinateComparisonResidual S v M) :=
  Iff.rfl

theorem affineChartCoordinateComparisonResidual_affineRing
    (M : SourcePsiIntegralModelData S v)
    (R : AffineChartCoordinateComparisonResidual S v M) :
    R.affineRing = affineMinimalCoordinateRing S v M := R.affineRing_eq

theorem affineChartCoordinateComparisonResidual_chartRing
    (M : SourcePsiIntegralModelData S v)
    (R : AffineChartCoordinateComparisonResidual S v M) :
    R.chartRing = chartWeierstrassCoordinateRing S v M.curve := R.chartRing_eq

structure AffineClosedSubschemeChartResidual
    (M : SourcePsiIntegralModelData S v) where
  chartOpen : (properModelProjectiveSpace S v).Opens
  chartOpen_eq : chartOpen = projectiveAffineChartOpen S v
  closedSubscheme : Scheme.{u}
  closedSubscheme_eq_affine : Prop
  coordinateComparison : Prop

def AffineClosedSubschemeChartStatement (M : SourcePsiIntegralModelData S v) : Prop :=
  Nonempty (AffineClosedSubschemeChartResidual S v M)

theorem affineClosedSubschemeChartStatement_iff
    (M : SourcePsiIntegralModelData S v) :
    AffineClosedSubschemeChartStatement S v M ↔
      Nonempty (AffineClosedSubschemeChartResidual S v M) :=
  Iff.rfl

theorem affineClosedSubschemeChartResidual_chartOpen
    (M : SourcePsiIntegralModelData S v)
    (R : AffineClosedSubschemeChartResidual S v M) :
    R.chartOpen = projectiveAffineChartOpen S v := R.chartOpen_eq

structure AffineChartRegularityResidual
    (M : SourcePsiIntegralModelData S v) where
  closedSubscheme : Scheme.{u}
  regular : Prop
  localEquation : Prop
  componentComparison : Prop

def AffineChartRegularityStatement (M : SourcePsiIntegralModelData S v) : Prop :=
  Nonempty (AffineChartRegularityResidual S v M)

theorem affineChartRegularityStatement_iff
    (M : SourcePsiIntegralModelData S v) :
    AffineChartRegularityStatement S v M ↔
      Nonempty (AffineChartRegularityResidual S v M) :=
  Iff.rfl

theorem affineChartRegularityResidual_regular
    (M : SourcePsiIntegralModelData S v)
    (R : AffineChartRegularityResidual S v M) : R.regular := R.regular

theorem projectiveAffineChart_actual_and_residuals
    (M : SourcePsiIntegralModelData S v) :
    AffineChartEquationComparison S v ∧
      (AffineChartCoordinateComparisonStatement S v M ↔
        Nonempty (AffineChartCoordinateComparisonResidual S v M)) ∧
      (AffineClosedSubschemeChartStatement S v M ↔
        Nonempty (AffineClosedSubschemeChartResidual S v M)) ∧
      (AffineChartRegularityStatement S v M ↔
        Nonempty (AffineChartRegularityResidual S v M)) :=
  ⟨affineChartEquationComparison_holds S v,
    affineChartCoordinateComparisonStatement_iff S v M,
    affineClosedSubschemeChartStatement_iff S v M,
    affineChartRegularityStatement_iff S v M⟩

/-- Membership in the actual chart D+(Z). -/
theorem mem_projectiveAffineChartOpen
    (x : properModelProjectiveSpace S v) :
    x ∈ projectiveAffineChartOpen S v ↔
      chartVariable S v ∉ x.asHomogeneousIdeal :=
  AlgebraicGeometry.Proj.mem_basicOpen _ _

theorem projectiveAffineChartOpen_eq_basicOpen :
    projectiveAffineChartOpen S v =
      AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin 3) (chartBase S v))
        (chartVariable S v) :=
  rfl

/-- The projective Weierstrass chart ideal. -/
def chartWeierstrassIdeal (W : WeierstrassCurve (chartBase S v)) :
    Ideal (chartAwayRing S v) :=
  Ideal.span {properModelWeierstrassPolynomial S v W}

theorem chartWeierstrassCoordinateRing_eq_quotient
    (W : WeierstrassCurve (chartBase S v)) :
    chartWeierstrassCoordinateRing S v W =
      chartAwayRing S v ⧸ chartWeierstrassIdeal S v W :=
  rfl

theorem affineMinimalChart_eq
    (M : SourcePsiIntegralModelData S v) :
    affineMinimalChart S v M = properModelAffineChart S v M :=
  rfl

theorem affineMinimalCoordinateRing_eq
    (M : SourcePsiIntegralModelData S v) :
    affineMinimalCoordinateRing S v M =
      WeierstrassCurve.Affine.CoordinateRing (affineMinimalChart S v M) :=
  rfl

theorem affineChartEquationComparison_of_model
    (M : SourcePsiIntegralModelData S v) :
    AffineChartEquationComparison S v :=
  affineChartEquationComparison_holds S v

theorem projectiveAffineChartOpenImmersion_isOpen :
    IsOpenImmersion (projectiveAffineChartOpenImmersion S v) :=
  projectiveAffineChartOpen_isOpen S v

theorem projectiveAffineChartOpenImmersion_type :
    projectiveAffineChartOpen S v ⟶ properModelProjectiveSpace S v :=
  projectiveAffineChartOpenImmersion S v

theorem projectiveAffineChartToSpec_type :
    projectiveAffineChartOpen S v ⟶
      Spec (CommRingCat.of (chartAwayRing S v)) :=
  projectiveAffineChartToSpec S v

structure ProjectiveAffineChartComparisonData
    (M : SourcePsiIntegralModelData S v) where
  equationComparison : AffineChartEquationComparison S v
  chartOpen : (properModelProjectiveSpace S v).Opens
  chartOpen_eq : chartOpen = projectiveAffineChartOpen S v
  coordinateResidual : Prop
  closedSubschemeResidual : Prop
  regularityResidual : Prop

noncomputable def projectiveAffineChartComparisonData
    (M : SourcePsiIntegralModelData S v) :
    ProjectiveAffineChartComparisonData S v M where
  equationComparison := affineChartEquationComparison_holds S v
  chartOpen := projectiveAffineChartOpen S v
  chartOpen_eq := rfl
  coordinateResidual := AffineChartCoordinateComparisonStatement S v M
  closedSubschemeResidual := AffineClosedSubschemeChartStatement S v M
  regularityResidual := AffineChartRegularityStatement S v M

theorem projectiveAffineChartComparisonData_equation
    (M : SourcePsiIntegralModelData S v) :
    (projectiveAffineChartComparisonData S v M).equationComparison :=
  (projectiveAffineChartComparisonData S v M).equationComparison

theorem projectiveAffineChartComparisonData_chartOpen
    (M : SourcePsiIntegralModelData S v) :
    (projectiveAffineChartComparisonData S v M).chartOpen =
      projectiveAffineChartOpen S v :=
  rfl

theorem projectiveAffineChartComparisonData_coordinateResidual
    (M : SourcePsiIntegralModelData S v) :
    (projectiveAffineChartComparisonData S v M).coordinateResidual =
      AffineChartCoordinateComparisonStatement S v M :=
  rfl

theorem projectiveAffineChartComparisonData_closedSubschemeResidual
    (M : SourcePsiIntegralModelData S v) :
    (projectiveAffineChartComparisonData S v M).closedSubschemeResidual =
      AffineClosedSubschemeChartStatement S v M :=
  rfl

theorem projectiveAffineChartComparisonData_regularityResidual
    (M : SourcePsiIntegralModelData S v) :
    (projectiveAffineChartComparisonData S v M).regularityResidual =
      AffineChartRegularityStatement S v M :=
  rfl

theorem projectiveAffineChartComparisonData_actual_chart_eq
    (M : SourcePsiIntegralModelData S v) :
    (projectiveAffineChartComparisonData S v M).chartOpen =
      projectiveAffineChartOpen S v :=
  rfl

theorem projectiveAffineChartComparisonData_equationComparison
    (M : SourcePsiIntegralModelData S v) :
    AffineChartEquationComparison S v :=
  (projectiveAffineChartComparisonData S v M).equationComparison

theorem projectiveAffineChartComparisonData_actual_and_residuals
    (M : SourcePsiIntegralModelData S v) :
    AffineChartEquationComparison S v ∧
      AffineChartCoordinateComparisonStatement S v M ∧
      AffineClosedSubschemeChartStatement S v M ∧
      AffineChartRegularityStatement S v M :=
  ⟨affineChartEquationComparison_holds S v,
    (projectiveAffineChartComparisonData S v M).coordinateResidual,
    (projectiveAffineChartComparisonData S v M).closedSubschemeResidual,
    (projectiveAffineChartComparisonData S v M).regularityResidual⟩

theorem projectiveAffineChartComparisonData_chart_open_mem
    (M : SourcePsiIntegralModelData S v)
    (x : properModelProjectiveSpace S v) :
    x ∈ (projectiveAffineChartComparisonData S v M).chartOpen ↔
      chartVariable S v ∉ x.asHomogeneousIdeal :=
  mem_projectiveAffineChartOpen S v x

theorem projectiveAffineChartComparisonData_coordinate_statement
    (M : SourcePsiIntegralModelData S v) :
    AffineChartCoordinateComparisonStatement S v M :=
  (projectiveAffineChartComparisonData S v M).coordinateResidual

theorem projectiveAffineChartComparisonData_closed_statement
    (M : SourcePsiIntegralModelData S v) :
    AffineClosedSubschemeChartStatement S v M :=
  (projectiveAffineChartComparisonData S v M).closedSubschemeResidual

theorem projectiveAffineChartComparisonData_regularity_statement
    (M : SourcePsiIntegralModelData S v) :
    AffineChartRegularityStatement S v M :=
  (projectiveAffineChartComparisonData S v M).regularityResidual

end LeanFormal.IUT.SourcePsiProjectiveAffineChartComparison
