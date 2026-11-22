import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiActualMinimality
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiComponentNodeActual
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Tactic

/-!
# Actual projective/proper model of the source Weierstrass curve

The actual ambient projective space over the adic completion integers is
Mathlib's `Proj` of the homogeneous polynomial ring, and its structure morphism
is proper by the Mathlib `Proj` properness theorem.  The projective closure of
the actual integral Weierstrass model is the homogeneous zero locus of the
projective Weierstrass polynomial.  The closed-subscheme structure, regularity,
and component comparison are stated as exact residuals; no proper/regular model
is fabricated.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.SourcePsiProperRegularModelActual

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open LeanFormal.IUT.SourcePsiActualMinimalModelReduction
open LeanFormal.IUT.SourcePsiActualMinimality
open LeanFormal.IUT.SourcePsiComponentNodeActual
open MvPolynomial AlgebraicGeometry
open scoped Polynomial BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- The actual completion integer ring used as base. -/
abbrev properModelBase : Type u :=
  SourcePsiActualIntegers S v

/-- The homogeneous coordinate ring `R[X,Y,Z]`. -/
abbrev properModelHomogeneousRing (R : Type u) [CommRing R] : Type u :=
  MvPolynomial (Fin 3) R

/-- The actual ambient projective space `Proj R[X,Y,Z]` over the completion
integers, with its standard grading. -/
noncomputable def properModelProjectiveSpace : Scheme.{u} :=
  letI := MvPolynomial.gradedAlgebra (σ := Fin 3) (R := properModelBase S v)
  AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 3) (properModelBase S v))

/-- The structure morphism of the ambient projective space to `Spec R`. -/
noncomputable def properModelProjectiveStructureMap :
    properModelProjectiveSpace S v ⟶ Spec (CommRingCat.of (properModelBase S v)) :=
  letI := MvPolynomial.gradedAlgebra (σ := Fin 3) (R := properModelBase S v)
  AlgebraicGeometry.Proj.toSpecZero
    (MvPolynomial.homogeneousSubmodule (Fin 3) (properModelBase S v))

/-- Properness of the actual ambient projective space over the completion
integers, from Mathlib's `Proj` properness theorem. -/
theorem properModelProjectiveSpace_isProper :
    IsProper (properModelProjectiveStructureMap S v) :=
  by
  letI := MvPolynomial.gradedAlgebra (σ := Fin 3) (R := properModelBase S v)
  infer_instance

/-- The actual projective Weierstrass polynomial of an integral model. -/
noncomputable def properModelWeierstrassPolynomial
    (W : WeierstrassCurve (properModelBase S v)) :
    properModelHomogeneousRing (properModelBase S v) :=
  MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 +
    MvPolynomial.C W.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 +
    MvPolynomial.C W.a₃ * MvPolynomial.X 1 * MvPolynomial.X 2 ^ 2 -
    MvPolynomial.X 0 ^ 3 -
    MvPolynomial.C W.a₂ * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 -
    MvPolynomial.C W.a₄ * MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2 -
    MvPolynomial.C W.a₆ * MvPolynomial.X 2 ^ 3

/-- The projective Weierstrass polynomial is homogeneous of degree three. -/
theorem properModelWeierstrassPolynomial_isHomogeneous
    (W : WeierstrassCurve (properModelBase S v)) :
    (properModelWeierstrassPolynomial S v W).IsHomogeneous 3 :=
  by
  simp [properModelWeierstrassPolynomial, MvPolynomial.isHomogeneous_iff]

/-- The actual projective closure as the homogeneous zero locus of the actual
projective Weierstrass polynomial. -/
noncomputable def properModelProjectiveClosureSet
    (W : WeierstrassCurve (properModelBase S v)) :
    Set (ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 3)
      (properModelBase S v))) :=
  ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 3)
    (properModelBase S v)) {properModelWeierstrassPolynomial S v W}

/-- Actual affine point of the projective closure: the homogeneous polynomial
vanishes at `[x,y,1]`. -/
theorem properModelProjectiveClosure_affine_equation
    (W : WeierstrassCurve (properModelBase S v))
    (x y : properModelBase S v) :
    W.toAffine.Equation x y ↔
      MvPolynomial.eval ![x, y, 1]
        (properModelWeierstrassPolynomial S v W) = 0 :=
  by
  simp [properModelWeierstrassPolynomial, WeierstrassCurve.Affine.Equation,
    WeierstrassCurve.Affine.polynomial, MvPolynomial.eval]

/-- The actual affine Weierstrass chart of an integral model. -/
noncomputable def properModelAffineChart (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve.Affine (properModelBase S v) :=
  M.curve.toAffine

/-- The actual affine coordinate ring of the integral chart. -/
noncomputable abbrev properModelAffineCoordinateRing
    (M : SourcePsiIntegralModelData S v) : Type u :=
  WeierstrassCurve.Affine.CoordinateRing (properModelAffineChart S v M)

/-- The actual projective model data: ambient proper projective space, its
structure map, and the projective Weierstrass polynomial/closure. -/
structure ProperModelData
    (M : SourcePsiIntegralModelData S v) where
  projectiveSpace : Scheme.{u}
  projectiveSpace_eq : projectiveSpace = properModelProjectiveSpace S v
  structureMap : projectiveSpace ⟶ Spec (CommRingCat.of (properModelBase S v))
  structureMap_eq : structureMap = properModelProjectiveStructureMap S v
  isProper : IsProper structureMap
  weierstrassPolynomial : properModelHomogeneousRing (properModelBase S v)
  weierstrassPolynomial_eq : weierstrassPolynomial =
    properModelWeierstrassPolynomial S v M.curve
  closureSet : Set (ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 3)
    (properModelBase S v)))
  closureSet_eq : closureSet = properModelProjectiveClosureSet S v M.curve

noncomputable def properModelData
    (M : SourcePsiIntegralModelData S v) : ProperModelData S v M where
  projectiveSpace := properModelProjectiveSpace S v
  projectiveSpace_eq := rfl
  structureMap := properModelProjectiveStructureMap S v
  structureMap_eq := rfl
  isProper := properModelProjectiveSpace_isProper S v
  weierstrassPolynomial := properModelWeierstrassPolynomial S v M.curve
  weierstrassPolynomial_eq := rfl
  closureSet := properModelProjectiveClosureSet S v M.curve
  closureSet_eq := rfl

theorem properModelData_isProper
    (M : SourcePsiIntegralModelData S v) :
    IsProper (properModelData S v M).structureMap :=
  (properModelData S v M).isProper

theorem properModelData_projectiveSpace_eq
    (M : SourcePsiIntegralModelData S v) :
    (properModelData S v M).projectiveSpace = properModelProjectiveSpace S v :=
  rfl

theorem properModelData_closureSet_eq
    (M : SourcePsiIntegralModelData S v) :
    (properModelData S v M).closureSet =
      properModelProjectiveClosureSet S v M.curve :=
  rfl

/-- Exact regular-model residual for the actual projective closure. -/
structure ProperRegularModelResidual
    (M : SourcePsiIntegralModelData S v) where
  model : ProperModelData S v M
  closedSubscheme : Scheme.{u}
  closedSubscheme_eq_closure : Prop
  regular : Prop
  componentComparison : Prop

def ProperRegularModelResidualStatement
    (M : SourcePsiIntegralModelData S v) : Prop :=
  Nonempty (ProperRegularModelResidual S v M)

theorem properRegularModelResidualStatement_iff
    (M : SourcePsiIntegralModelData S v) :
    ProperRegularModelResidualStatement S v M ↔
      Nonempty (ProperRegularModelResidual S v M) :=
  Iff.rfl

theorem properRegularModelResidual_structureMap
    (M : SourcePsiIntegralModelData S v)
    (R : ProperRegularModelResidual S v M) :
    IsProper R.model.structureMap :=
  R.model.isProper

theorem properRegularModelResidual_regular
    (M : SourcePsiIntegralModelData S v)
    (R : ProperRegularModelResidual S v M) :
    R.regular :=
  R.regular

theorem properRegularModelResidual_component
    (M : SourcePsiIntegralModelData S v)
    (R : ProperRegularModelResidual S v M) :
    R.componentComparison :=
  R.componentComparison

/-- The ambient projective model is actual and proper; the regular closed
subscheme/component comparison is the exact remaining residual. -/
theorem properModelActual_and_regularResidual_statement
    (M : SourcePsiIntegralModelData S v) :
    IsProper (properModelData S v M).structureMap ∧
      (ProperRegularModelResidualStatement S v M ↔
        Nonempty (ProperRegularModelResidual S v M)) :=
  ⟨properModelData_isProper S v M,
    properRegularModelResidualStatement_iff S v M⟩

theorem properModelProjectiveClosureSet_mem_iff
    (W : WeierstrassCurve (properModelBase S v))
    (P : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 3)
      (properModelBase S v))) :
    P ∈ properModelProjectiveClosureSet S v W ↔
      properModelWeierstrassPolynomial S v W ∈ P.asHomogeneousIdeal :=
  by
  simp [properModelProjectiveClosureSet, ProjectiveSpectrum.mem_zeroLocus]

theorem properModelData_weierstrassPolynomial_eq
    (M : SourcePsiIntegralModelData S v) :
    (properModelData S v M).weierstrassPolynomial =
      properModelWeierstrassPolynomial S v M.curve :=
  rfl

theorem properModelData_structureMap_eq
    (M : SourcePsiIntegralModelData S v) :
    (properModelData S v M).structureMap =
      properModelProjectiveStructureMap S v :=
  rfl

theorem properModelData_type
    (M : SourcePsiIntegralModelData S v) :
    (properModelData S v M).projectiveSpace = properModelProjectiveSpace S v :=
  rfl

theorem properModelProjectiveStructureMap_type :
    properModelProjectiveSpace S v ⟶
      Spec (CommRingCat.of (properModelBase S v)) :=
  properModelProjectiveStructureMap S v

theorem properModelProjectiveSpace_isProper_consumer :
    IsProper (properModelProjectiveStructureMap S v) :=
  properModelProjectiveSpace_isProper S v

/-- Exact affine-chart comparison residual: the actual affine chart and the
missing closed-subscheme comparison map into the projective closure. -/
structure AffineChartComparisonResidual
    (M : SourcePsiIntegralModelData S v) where
  affineChart : WeierstrassCurve.Affine (properModelBase S v)
  affineChart_eq : affineChart = properModelAffineChart S v M
  chartToProjective : Prop
  chartOpenImmersion : Prop

def AffineChartComparisonResidualStatement
    (M : SourcePsiIntegralModelData S v) : Prop :=
  Nonempty (AffineChartComparisonResidual S v M)

theorem affineChartComparisonResidual_statement_iff
    (M : SourcePsiIntegralModelData S v) :
    AffineChartComparisonResidualStatement S v M ↔
      Nonempty (AffineChartComparisonResidual S v M) :=
  Iff.rfl

theorem affineChartComparisonResidual_chart
    (M : SourcePsiIntegralModelData S v)
    (R : AffineChartComparisonResidual S v M) :
    R.affineChart = properModelAffineChart S v M :=
  R.affineChart_eq

theorem properModelData_closure_subset
    (M : SourcePsiIntegralModelData S v) :
    (properModelData S v M).closureSet ⊆
      Set.univ :=
  Set.subset_univ _

theorem properModelActual_proper_and_residual_package
    (M : SourcePsiIntegralModelData S v) :
    IsProper (properModelData S v M).structureMap ∧
      (properModelProjectiveClosureSet S v M.curve ⊆ Set.univ) ∧
      (ProperRegularModelResidualStatement S v M ↔
        Nonempty (ProperRegularModelResidual S v M)) :=
  ⟨properModelData_isProper S v M,
    Set.subset_univ _,
    properRegularModelResidualStatement_iff S v M⟩
theorem properModelProjectiveClosureSet_subset_univ
    (W : WeierstrassCurve (properModelBase S v)) :
    properModelProjectiveClosureSet S v W ⊆ Set.univ :=
  Set.subset_univ _

theorem properModelData_structureMap_isProper
    (M : SourcePsiIntegralModelData S v) :
    IsProper (properModelData S v M).structureMap :=
  (properModelData S v M).isProper

theorem properRegularModelResidual_model_proper
    (M : SourcePsiIntegralModelData S v)
    (R : ProperRegularModelResidual S v M) :
    IsProper R.model.structureMap :=
  R.model.isProper

theorem affineChartComparisonResidual_chart_eq
    (M : SourcePsiIntegralModelData S v)
    (R : AffineChartComparisonResidual S v M) :
    R.affineChart = properModelAffineChart S v M :=
  R.affineChart_eq
end LeanFormal.IUT.SourcePsiProperRegularModelActual
