import LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectiveIdealSheafGluingInputProof
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Tactic

/-!
# Basic-open compatibility for the actual global ideal family

The global affine-open ideal family is the intersection of the chart-localized
ideals over the three standard charts.  The forward basic-open inclusion follows
from functoriality of restriction and the chart definition.  The reverse
inclusion is the exact localization/gluing lemma not provided by the frozen
API; it is isolated.  Conditional on this exact lemma, the
ProjectiveIdealSheafGluingInput and hence the actual global non-reduced ideal
sheaf are constructed.  No fake sheaf is produced.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.GlobalIdealFamilyBasicOpenProof

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiActualMinimalModelReduction
open LeanFormal.IUT.SourcePsiActualMinimality
open LeanFormal.IUT.SourcePsiProperRegularModelActual
open LeanFormal.IUT.SourcePsiProjectiveAffineChartComparison
open LeanFormal.IUT.SourcePsiProjectiveClosedModelConstruct
open LeanFormal.IUT.SourcePsiProjectiveIdealSheaf
open LeanFormal.IUT.SourcePsiNonreducedIdealSheaf
open LeanFormal.IUT.GlobalNonreducedIdealSheafConstruction
open LeanFormal.IUT.GlobalNonreducedIdealSheafGluing
open LeanFormal.IUT.ProjectiveIdealSheafGluingInputProof
open MvPolynomial AlgebraicGeometry
open scoped Polynomial BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

abbrev basicOpenBase : Type u := gluingBase S v
abbrev basicOpenProj : Scheme.{u} := gluingProj S v

/-- The forward inclusion of the basic-open map for the global family. -/
def GlobalIdealFamilyBasicOpenForward
    (W : WeierstrassCurve (basicOpenBase S v)) : Prop :=
  ∀ (U : (basicOpenProj S v).affineOpens)
    (f : Γ(basicOpenProj S v, U)),
    (globalIdealFamily S v W U).map
        ((basicOpenProj S v).presheaf.map
          (homOfLE ((basicOpenProj S v).basicOpen_le f)).op).hom ≤
      globalIdealFamily S v W
        ((basicOpenProj S v).affineBasicOpen f)

/-- The reverse inclusion of the basic-open map for the global family.  This is
the exact localization/gluing lemma isolated as the residual. -/
def GlobalIdealFamilyBasicOpenReverse
    (W : WeierstrassCurve (basicOpenBase S v)) : Prop :=
  ∀ (U : (basicOpenProj S v).affineOpens)
    (f : Γ(basicOpenProj S v, U)),
    globalIdealFamily S v W
        ((basicOpenProj S v).affineBasicOpen f) ≤
      (globalIdealFamily S v W U).map
        ((basicOpenProj S v).presheaf.map
          (homOfLE ((basicOpenProj S v).basicOpen_le f)).op).hom

/-- The exact basic-open equality statement for the global family. -/
def GlobalIdealFamilyBasicOpenEquality
    (W : WeierstrassCurve (basicOpenBase S v)) : Prop :=
  ∀ (U : (basicOpenProj S v).affineOpens)
    (f : Γ(basicOpenProj S v, U)),
    (globalIdealFamily S v W U).map
        ((basicOpenProj S v).presheaf.map
          (homOfLE ((basicOpenProj S v).basicOpen_le f)).op).hom =
      globalIdealFamily S v W
        ((basicOpenProj S v).affineBasicOpen f)

/-- Forward inclusion from functoriality of restriction and the chart-defined
family. -/
theorem globalIdealFamilyBasicOpenForward_holds
    (W : WeierstrassCurve (basicOpenBase S v)) :
    GlobalIdealFamilyBasicOpenForward S v W :=
  by
  intro U f
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap] at hx ⊢
  -- The family condition is componentwise over the charts; restriction to the
  -- basic open commutes with each chart restriction.
  exact hx

/-- The reverse inclusion is the exact residual lemma. -/
structure GlobalIdealFamilyBasicOpenReverseLemma
    (W : WeierstrassCurve (basicOpenBase S v)) where
  reverse : GlobalIdealFamilyBasicOpenReverse S v W

theorem globalIdealFamilyBasicOpenReverseLemma_iff
    (W : WeierstrassCurve (basicOpenBase S v)) :
    Nonempty (GlobalIdealFamilyBasicOpenReverseLemma S v W) ↔
      GlobalIdealFamilyBasicOpenReverse S v W :=
  ⟨fun R => R.some.reverse, fun h => ⟨⟨h⟩⟩⟩

/-- Equality is equivalent to the forward inclusion together with the exact
reverse residual. -/
theorem globalIdealFamilyBasicOpenEquality_iff
    (W : WeierstrassCurve (basicOpenBase S v)) :
    GlobalIdealFamilyBasicOpenEquality S v W ↔
      GlobalIdealFamilyBasicOpenForward S v W ∧
        GlobalIdealFamilyBasicOpenReverse S v W :=
  by
  constructor
  · intro h
    exact ⟨fun U f => (h U f).le,
      fun U f => (h U f).ge⟩
  · rintro ⟨hforward, hreverse⟩ U f
    exact le_antisymm (hforward U f) (hreverse U f)

/-- The exact residual, now expressed as the reverse inclusion. -/
def GlobalIdealFamilyBasicOpenResidualStatement
    (W : WeierstrassCurve (basicOpenBase S v)) : Prop :=
  GlobalIdealFamilyBasicOpenReverse S v W

theorem globalIdealFamilyBasicOpenResidualStatement_iff
    (W : WeierstrassCurve (basicOpenBase S v)) :
    GlobalIdealFamilyBasicOpenResidualStatement S v W ↔
      GlobalIdealFamilyBasicOpenReverse S v W :=
  Iff.rfl

/-- Chart-local forward inclusion: on a standard chart the family is the chart
ideal, so restriction to a basic open inside the chart is the chart ideal
restricted. -/
theorem globalIdealFamilyBasicOpen_forward_chart
    (W : WeierstrassCurve (basicOpenBase S v)) (j : Fin 3)
    (f : Γ(basicOpenProj S v, projectiveStandardChartAffine S v j)) :
    (globalIdealFamily S v W (projectiveStandardChartAffine S v j)).map
        ((basicOpenProj S v).presheaf.map
          (homOfLE ((basicOpenProj S v).basicOpen_le f)).op).hom ≤
      globalIdealFamily S v W
        ((basicOpenProj S v).affineBasicOpen f) :=
  globalIdealFamilyBasicOpenForward_holds S v W
    (projectiveStandardChartAffine S v j) f

/-- Chart-local reverse inclusion, conditional on the exact reverse lemma. -/
theorem globalIdealFamilyBasicOpen_reverse_chart
    (W : WeierstrassCurve (basicOpenBase S v))
    (R : GlobalIdealFamilyBasicOpenReverseLemma S v W) (j : Fin 3)
    (f : Γ(basicOpenProj S v, projectiveStandardChartAffine S v j)) :
    globalIdealFamily S v W
        ((basicOpenProj S v).affineBasicOpen f) ≤
      (globalIdealFamily S v W (projectiveStandardChartAffine S v j)).map
        ((basicOpenProj S v).presheaf.map
          (homOfLE ((basicOpenProj S v).basicOpen_le f)).op).hom :=
  R.reverse (projectiveStandardChartAffine S v j) f

/-- The basic-open gluing residual used by the conditional ideal-sheaf
construction. -/
noncomputable def globalIdealFamilyBasicOpenResidualOfReverse
    (W : WeierstrassCurve (basicOpenBase S v))
    (R : GlobalIdealFamilyBasicOpenReverseLemma S v W) :
    GlobalIdealFamilyBasicOpenResidual S v W where
  map_ideal_basicOpen := fun U f =>
    le_antisymm (globalIdealFamilyBasicOpenForward_holds S v W U f)
      (R.reverse U f)

theorem globalIdealFamilyBasicOpenResidualOfReverse_map
    (W : WeierstrassCurve (basicOpenBase S v))
    (R : GlobalIdealFamilyBasicOpenReverseLemma S v W)
    (U : (basicOpenProj S v).affineOpens)
    (f : Γ(basicOpenProj S v, U)) :
    (globalIdealFamilyBasicOpenResidualOfReverse S v W R).map_ideal_basicOpen
        U f =
      le_antisymm (globalIdealFamilyBasicOpenForward_holds S v W U f)
        (R.reverse U f) :=
  rfl

/-- Conditional actual gluing input from the exact reverse lemma. -/
noncomputable def projectiveIdealSheafGluingInputOfReverse
    (W : WeierstrassCurve (basicOpenBase S v))
    (R : GlobalIdealFamilyBasicOpenReverseLemma S v W) :
    ProjectiveIdealSheafGluingInput S v W :=
  projectiveIdealSheafGluingInputOfFamily S v W
    (globalIdealFamilyBasicOpenResidualOfReverse S v W R)

theorem projectiveIdealSheafGluingInputOfReverse_chart
    (W : WeierstrassCurve (basicOpenBase S v))
    (R : GlobalIdealFamilyBasicOpenReverseLemma S v W) (i : Fin 3) :
    (projectiveIdealSheafGluingInputOfReverse S v W R).ideal
        (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v W i :=
  globalIdealFamily_chart S v W i

theorem projectiveIdealSheafGluingInputOfReverse_map
    (W : WeierstrassCurve (basicOpenBase S v))
    (R : GlobalIdealFamilyBasicOpenReverseLemma S v W)
    (U : (basicOpenProj S v).affineOpens)
    (f : Γ(basicOpenProj S v, U)) :
    ((projectiveIdealSheafGluingInputOfReverse S v W R).ideal U).map
        ((basicOpenProj S v).presheaf.map
          (homOfLE ((basicOpenProj S v).basicOpen_le f)).op).hom =
      (projectiveIdealSheafGluingInputOfReverse S v W R).ideal
        ((basicOpenProj S v).affineBasicOpen f) :=
  (projectiveIdealSheafGluingInputOfReverse S v W R).map_ideal_basicOpen U f

/-- Conditional actual global non-reduced ideal sheaf, given the exact reverse
inclusion lemma. -/
noncomputable def globalNonreducedIdealSheafOfReverse
    (W : WeierstrassCurve (basicOpenBase S v))
    (R : GlobalIdealFamilyBasicOpenReverseLemma S v W) :
    (basicOpenProj S v).IdealSheafData :=
  gluedIdealSheaf S v W (projectiveIdealSheafGluingInputOfReverse S v W R)

theorem globalNonreducedIdealSheafOfReverse_ideal
    (W : WeierstrassCurve (basicOpenBase S v))
    (R : GlobalIdealFamilyBasicOpenReverseLemma S v W)
    (U : (basicOpenProj S v).affineOpens) :
    (globalNonreducedIdealSheafOfReverse S v W R).ideal U =
      globalIdealFamily S v W U :=
  rfl

theorem globalNonreducedIdealSheafOfReverse_chart
    (W : WeierstrassCurve (basicOpenBase S v))
    (R : GlobalIdealFamilyBasicOpenReverseLemma S v W) (i : Fin 3) :
    (globalNonreducedIdealSheafOfReverse S v W R).ideal
        (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v W i :=
  globalIdealFamily_chart S v W i

theorem globalIdealFamilyBasicOpen_actual_and_exactReverse
    (W : WeierstrassCurve (basicOpenBase S v)) :
    GlobalIdealFamilyBasicOpenForward S v W ∧
      (GlobalIdealFamilyBasicOpenEquality S v W ↔
        GlobalIdealFamilyBasicOpenForward S v W ∧
          GlobalIdealFamilyBasicOpenReverse S v W) :=
  ⟨globalIdealFamilyBasicOpenForward_holds S v W,
    globalIdealFamilyBasicOpenEquality_iff S v W⟩

theorem globalIdealFamilyBasicOpenForward_type
    (W : WeierstrassCurve (basicOpenBase S v)) :
    GlobalIdealFamilyBasicOpenForward S v W :=
  globalIdealFamilyBasicOpenForward_holds S v W

theorem globalIdealFamilyBasicOpenForward_apply
    (W : WeierstrassCurve (basicOpenBase S v))
    (U : (basicOpenProj S v).affineOpens)
    (f : Γ(basicOpenProj S v, U)) :
    (globalIdealFamily S v W U).map
        ((basicOpenProj S v).presheaf.map
          (homOfLE ((basicOpenProj S v).basicOpen_le f)).op).hom ≤
      globalIdealFamily S v W
        ((basicOpenProj S v).affineBasicOpen f) :=
  globalIdealFamilyBasicOpenForward_holds S v W U f

theorem globalIdealFamilyBasicOpenReverse_statement
    (W : WeierstrassCurve (basicOpenBase S v)) :
    GlobalIdealFamilyBasicOpenResidualStatement S v W ↔
      GlobalIdealFamilyBasicOpenReverse S v W :=
  Iff.rfl

theorem globalIdealFamilyBasicOpenReverseLemma_type
    (W : WeierstrassCurve (basicOpenBase S v)) :
    Nonempty (GlobalIdealFamilyBasicOpenReverseLemma S v W) ↔
      GlobalIdealFamilyBasicOpenReverse S v W :=
  globalIdealFamilyBasicOpenReverseLemma_iff S v W

theorem globalIdealFamilyBasicOpenEquality_forward
    (W : WeierstrassCurve (basicOpenBase S v)) :
    GlobalIdealFamilyBasicOpenEquality S v W →
      GlobalIdealFamilyBasicOpenForward S v W :=
  fun h => (globalIdealFamilyBasicOpenEquality_iff S v W).mp h |>.1

theorem globalIdealFamilyBasicOpenEquality_reverse
    (W : WeierstrassCurve (basicOpenBase S v)) :
    GlobalIdealFamilyBasicOpenEquality S v W →
      GlobalIdealFamilyBasicOpenReverse S v W :=
  fun h => (globalIdealFamilyBasicOpenEquality_iff S v W).mp h |>.2

theorem projectiveIdealSheafGluingInputOfReverse_ideal
    (W : WeierstrassCurve (basicOpenBase S v))
    (R : GlobalIdealFamilyBasicOpenReverseLemma S v W)
    (U : (basicOpenProj S v).affineOpens) :
    (projectiveIdealSheafGluingInputOfReverse S v W R).ideal U =
      globalIdealFamily S v W U :=
  rfl

theorem globalNonreducedIdealSheafOfReverse_support
    (W : WeierstrassCurve (basicOpenBase S v))
    (R : GlobalIdealFamilyBasicOpenReverseLemma S v W) :
    (globalNonreducedIdealSheafOfReverse S v W R).support =
      ⟨⋂ U, (basicOpenProj S v).zeroLocus (U := U.1)
        (globalIdealFamily S v W U),
        (globalNonreducedIdealSheafOfReverse S v W R).isClosed_supportSet⟩ :=
  rfl

abbrev globalNonreducedIdealSheafOfReverseClosedSubscheme
    (W : WeierstrassCurve (basicOpenBase S v))
    (R : GlobalIdealFamilyBasicOpenReverseLemma S v W) : Scheme.{u} :=
  (globalNonreducedIdealSheafOfReverse S v W R).subscheme

theorem globalNonreducedIdealSheafOfReverse_subscheme_range
    (W : WeierstrassCurve (basicOpenBase S v))
    (R : GlobalIdealFamilyBasicOpenReverseLemma S v W) :
    Set.range (globalNonreducedIdealSheafOfReverse S v W R).subschemeι =
      ((globalNonreducedIdealSheafOfReverse S v W R).support :
        Set (basicOpenProj S v)) :=
  (globalNonreducedIdealSheafOfReverse S v W R).range_subschemeι

theorem globalIdealFamilyBasicOpen_residual_from_reverse
    (W : WeierstrassCurve (basicOpenBase S v))
    (R : GlobalIdealFamilyBasicOpenReverseLemma S v W) :
    GlobalIdealFamilyBasicOpenResidualStatement S v W :=
  R.reverse

theorem globalIdealFamilyBasicOpen_conditional_construction
    (W : WeierstrassCurve (basicOpenBase S v))
    (R : GlobalIdealFamilyBasicOpenReverseLemma S v W) :
    (∀ i : Fin 3,
      (globalNonreducedIdealSheafOfReverse S v W R).ideal
        (projectiveStandardChartAffine S v i) =
        projectiveNonreducedChartIdeal S v W i) ∧
      (GlobalIdealFamilyBasicOpenResidualStatement S v W ↔
        GlobalIdealFamilyBasicOpenReverse S v W) :=
  ⟨fun i => globalNonreducedIdealSheafOfReverse_chart S v W R i,
    Iff.rfl⟩

end LeanFormal.IUT.GlobalIdealFamilyBasicOpenProof
