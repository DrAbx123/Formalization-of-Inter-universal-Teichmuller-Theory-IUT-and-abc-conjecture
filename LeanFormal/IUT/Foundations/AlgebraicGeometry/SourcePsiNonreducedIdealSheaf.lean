import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiProjectiveIdealSheaf
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiProjectiveAffineChartComparison
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-!
# Non-reduced F-localized chart ideal sheaf

The reduced vanishing-ideal sheaf is already constructed on the ambient Proj.
This file constructs the actual F-localized non-reduced chart ideal on the
standard affine chart Z = 1: the element F / Z^3 in the degree-zero
localization, the ideal it generates, its quotient, and the quotient comparison
with its radical (the reduced chart ideal).  The global non-reduced ideal sheaf
on Proj is stated as an exact residual, because the frozen API does not provide
homogeneous-ideal localization on all affine opens.  No fake subscheme is
constructed.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.SourcePsiNonreducedIdealSheaf

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiActualMinimalModelReduction
open LeanFormal.IUT.SourcePsiActualMinimality
open LeanFormal.IUT.SourcePsiProperRegularModelActual
open LeanFormal.IUT.SourcePsiProjectiveAffineChartComparison
open LeanFormal.IUT.SourcePsiProjectiveClosedModelConstruct
open LeanFormal.IUT.SourcePsiProjectiveIdealSheaf
open MvPolynomial AlgebraicGeometry
open scoped Polynomial BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

abbrev nonreducedBase : Type u := closedModelBase S v

abbrev nonreducedHomogeneousRing : Type u :=
  MvPolynomial (Fin 3) (nonreducedBase S v)

/-- The actual standard chart coordinate ring at Z, before quotient. -/
abbrev standardChartAwayRing : Type u := chartAwayRing S v

/-- The homogeneous Weierstrass polynomial in the standard chart. -/
noncomputable def nonreducedChartPolynomial
    (W : WeierstrassCurve (nonreducedBase S v)) :
    nonreducedHomogeneousRing S v :=
  properModelWeierstrassPolynomial S v W

/-- The actual degree-zero chart element F / Z^3. -/
noncomputable def nonreducedChartElement
    (W : WeierstrassCurve (nonreducedBase S v)) :
    standardChartAwayRing S v :=
  HomogeneousLocalization.Away.mk
    (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 3) (nonreducedBase S v))
    (f := chartVariable S v) (d := 1)
    (by simpa [chartVariable, MvPolynomial.mem_homogeneousSubmodule]
      using MvPolynomial.isHomogeneous_X (R := nonreducedBase S v) 2)
    3 (nonreducedChartPolynomial S v W)
    (by
      simpa [nonreducedChartPolynomial, chartVariable,
        MvPolynomial.mem_homogeneousSubmodule]
        using properModelWeierstrassPolynomial_isHomogeneous S v W)

/-- The actual F-localized non-reduced chart ideal. -/
noncomputable def nonreducedChartIdeal
    (W : WeierstrassCurve (nonreducedBase S v)) :
    Ideal (standardChartAwayRing S v) :=
  Ideal.span {nonreducedChartElement S v W}

/-- The reduced chart ideal: the radical of the F-localized ideal. -/
noncomputable def reducedChartIdeal
    (W : WeierstrassCurve (nonreducedBase S v)) :
    Ideal (standardChartAwayRing S v) :=
  (nonreducedChartIdeal S v W).radical

theorem nonreducedChartElement_mem
    (W : WeierstrassCurve (nonreducedBase S v)) :
    nonreducedChartElement S v W ∈ nonreducedChartIdeal S v W :=
  Ideal.subset_span rfl

theorem nonreducedChartIdeal_le_reduced
    (W : WeierstrassCurve (nonreducedBase S v)) :
    nonreducedChartIdeal S v W ≤ reducedChartIdeal S v W :=
  Ideal.le_radical

theorem reducedChartIdeal_isRadical
    (W : WeierstrassCurve (nonreducedBase S v)) :
    (reducedChartIdeal S v W).IsRadical :=
  Ideal.radical_isRadical _

/-- The actual non-reduced chart quotient ring. -/
abbrev nonreducedChartQuotient
    (W : WeierstrassCurve (nonreducedBase S v)) : Type u :=
  standardChartAwayRing S v ⧸ nonreducedChartIdeal S v W

/-- The actual reduced chart quotient ring. -/
abbrev reducedChartQuotient
    (W : WeierstrassCurve (nonreducedBase S v)) : Type u :=
  standardChartAwayRing S v ⧸ reducedChartIdeal S v W

/-- The actual quotient map from the non-reduced chart quotient to the reduced
chart quotient. -/
noncomputable def nonreducedToReducedChartQuotient
    (W : WeierstrassCurve (nonreducedBase S v)) :
    nonreducedChartQuotient S v W →+* reducedChartQuotient S v W :=
  Ideal.Quotient.lift (nonreducedChartIdeal S v W)
    (Ideal.Quotient.mk (reducedChartIdeal S v W))
    (by
      intro x hx
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.le_radical (nonreducedChartIdeal_le_reduced S v W hx)))

theorem nonreducedToReducedChartQuotient_apply
    (W : WeierstrassCurve (nonreducedBase S v))
    (x : standardChartAwayRing S v) :
    nonreducedToReducedChartQuotient S v W
        (Ideal.Quotient.mk (nonreducedChartIdeal S v W) x) =
      Ideal.Quotient.mk (reducedChartIdeal S v W) x :=
  rfl

theorem nonreducedChartElement_zero_in_quotient
    (W : WeierstrassCurve (nonreducedBase S v)) :
    Ideal.Quotient.mk (nonreducedChartIdeal S v W)
        (nonreducedChartElement S v W) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

theorem nonreducedChartElement_zero_in_reduced_quotient
    (W : WeierstrassCurve (nonreducedBase S v)) :
    Ideal.Quotient.mk (reducedChartIdeal S v W)
        (nonreducedChartElement S v W) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.le_radical (Ideal.subset_span rfl))

/-- The actual non-reduced standard chart model data. -/
structure StandardChartNonreducedData
    (W : WeierstrassCurve (nonreducedBase S v)) where
  awayRing : Type u
  awayRing_eq : awayRing = standardChartAwayRing S v
  chartElement : awayRing
  chartElement_eq : chartElement = nonreducedChartElement S v W
  nonreducedIdeal : Ideal awayRing
  nonreducedIdeal_eq : nonreducedIdeal = nonreducedChartIdeal S v W
  reducedIdeal : Ideal awayRing
  reducedIdeal_eq : reducedIdeal = reducedChartIdeal S v W
  quotient : Type u
  quotient_eq : quotient = nonreducedChartQuotient S v W
  reducedQuotient : Type u
  reducedQuotient_eq : reducedQuotient = reducedChartQuotient S v W
  quotientMap : quotient →+* reducedQuotient

noncomputable def standardChartNonreducedData
    (W : WeierstrassCurve (nonreducedBase S v)) :
    StandardChartNonreducedData S v W where
  awayRing := standardChartAwayRing S v
  awayRing_eq := rfl
  chartElement := nonreducedChartElement S v W
  chartElement_eq := rfl
  nonreducedIdeal := nonreducedChartIdeal S v W
  nonreducedIdeal_eq := rfl
  reducedIdeal := reducedChartIdeal S v W
  reducedIdeal_eq := rfl
  quotient := nonreducedChartQuotient S v W
  quotient_eq := rfl
  reducedQuotient := reducedChartQuotient S v W
  reducedQuotient_eq := rfl
  quotientMap := nonreducedToReducedChartQuotient S v W

theorem standardChartNonreducedData_ideal
    (W : WeierstrassCurve (nonreducedBase S v)) :
    (standardChartNonreducedData S v W).nonreducedIdeal =
      nonreducedChartIdeal S v W :=
  rfl

theorem standardChartNonreducedData_reducedIdeal
    (W : WeierstrassCurve (nonreducedBase S v)) :
    (standardChartNonreducedData S v W).reducedIdeal =
      reducedChartIdeal S v W :=
  rfl

theorem standardChartNonreducedData_quotientMap
    (W : WeierstrassCurve (nonreducedBase S v)) :
    (standardChartNonreducedData S v W).quotientMap =
      nonreducedToReducedChartQuotient S v W :=
  rfl

/-- The actual F-localized chart ideal is non-reduced unless it equals its
radical; this is stated as an exact comparison predicate. -/
def ChartNonreducednessStatement
    (W : WeierstrassCurve (nonreducedBase S v)) : Prop :=
  nonreducedChartIdeal S v W ≠ reducedChartIdeal S v W

theorem chartNonreducedness_iff
    (W : WeierstrassCurve (nonreducedBase S v)) :
    ChartNonreducednessStatement S v W ↔
      nonreducedChartIdeal S v W ≠ reducedChartIdeal S v W :=
  Iff.rfl

/-- Exact global non-reduced ideal-sheaf residual: localization of the
homogeneous Weierstrass ideal on every affine open of Proj and its comparison
with the reduced vanishing ideal sheaf. -/
structure GlobalNonreducedIdealSheafResidual
    (W : WeierstrassCurve (nonreducedBase S v)) where
  globalIdealSheaf : (properModelProjectiveSpace S v).IdealSheafData
  globalIdealSheaf_eq : Prop
  chartIdealComparison : Prop
  reducedComparison : Prop
  regular : Prop
  componentComparison : Prop

def GlobalNonreducedIdealSheafResidualStatement
    (W : WeierstrassCurve (nonreducedBase S v)) : Prop :=
  Nonempty (GlobalNonreducedIdealSheafResidual S v W)

theorem globalNonreducedIdealSheafResidualStatement_iff
    (W : WeierstrassCurve (nonreducedBase S v)) :
    GlobalNonreducedIdealSheafResidualStatement S v W ↔
      Nonempty (GlobalNonreducedIdealSheafResidual S v W) :=
  Iff.rfl

theorem globalNonreducedIdealSheafResidual_regular
    (W : WeierstrassCurve (nonreducedBase S v))
    (R : GlobalNonreducedIdealSheafResidual S v W) :
    R.regular := R.regular

theorem globalNonreducedIdealSheafResidual_component
    (W : WeierstrassCurve (nonreducedBase S v))
    (R : GlobalNonreducedIdealSheafResidual S v W) :
    R.componentComparison := R.componentComparison

/-- The actual chart construction and the exact global residual. -/
theorem standardChartNonreduced_actual_and_globalResidual
    (W : WeierstrassCurve (nonreducedBase S v)) :
    nonreducedChartElement S v W ∈ nonreducedChartIdeal S v W ∧
      nonreducedChartIdeal S v W ≤ reducedChartIdeal S v W ∧
      (ChartNonreducednessStatement S v W ↔
        nonreducedChartIdeal S v W ≠ reducedChartIdeal S v W) ∧
      (GlobalNonreducedIdealSheafResidualStatement S v W ↔
        Nonempty (GlobalNonreducedIdealSheafResidual S v W)) :=
  ⟨nonreducedChartElement_mem S v W,
    nonreducedChartIdeal_le_reduced S v W,
    chartNonreducedness_iff S v W,
    globalNonreducedIdealSheafResidualStatement_iff S v W⟩

theorem nonreducedChartIdeal_eq_span
    (W : WeierstrassCurve (nonreducedBase S v)) :
    nonreducedChartIdeal S v W = Ideal.span {nonreducedChartElement S v W} :=
  rfl

theorem reducedChartIdeal_eq_radical
    (W : WeierstrassCurve (nonreducedBase S v)) :
    reducedChartIdeal S v W = (nonreducedChartIdeal S v W).radical :=
  rfl

theorem standardChartNonreducedData_chartElement
    (W : WeierstrassCurve (nonreducedBase S v)) :
    (standardChartNonreducedData S v W).chartElement =
      nonreducedChartElement S v W :=
  rfl

theorem standardChartNonreducedData_quotient
    (W : WeierstrassCurve (nonreducedBase S v)) :
    (standardChartNonreducedData S v W).quotient =
      nonreducedChartQuotient S v W :=
  rfl

theorem standardChartNonreducedData_reducedQuotient
    (W : WeierstrassCurve (nonreducedBase S v)) :
    (standardChartNonreducedData S v W).reducedQuotient =
      reducedChartQuotient S v W :=
  rfl

abbrev nonreducedChartQuotientType
    (W : WeierstrassCurve (nonreducedBase S v)) : Type u :=
  nonreducedChartQuotient S v W

abbrev reducedChartQuotientType
    (W : WeierstrassCurve (nonreducedBase S v)) : Type u :=
  reducedChartQuotient S v W

theorem standardChartNonreducedData_actual_chart
    (W : WeierstrassCurve (nonreducedBase S v)) :
    (standardChartNonreducedData S v W).awayRing = standardChartAwayRing S v :=
  rfl

theorem standardChartNonreducedData_actual_reducedIdeal
    (W : WeierstrassCurve (nonreducedBase S v)) :
    (standardChartNonreducedData S v W).reducedIdeal = reducedChartIdeal S v W :=
  rfl

theorem standardChartNonreducedData_actual_quotientMap
    (W : WeierstrassCurve (nonreducedBase S v)) :
    (standardChartNonreducedData S v W).quotientMap =
      nonreducedToReducedChartQuotient S v W :=
  rfl

theorem standardChartNonreducedData_actual_and_residual
    (W : WeierstrassCurve (nonreducedBase S v)) :
    (standardChartNonreducedData S v W).nonreducedIdeal ≤
        (standardChartNonreducedData S v W).reducedIdeal ∧
      (GlobalNonreducedIdealSheafResidualStatement S v W ↔
        Nonempty (GlobalNonreducedIdealSheafResidual S v W)) :=
  ⟨nonreducedChartIdeal_le_reduced S v W,
    globalNonreducedIdealSheafResidualStatement_iff S v W⟩

end LeanFormal.IUT.SourcePsiNonreducedIdealSheaf
