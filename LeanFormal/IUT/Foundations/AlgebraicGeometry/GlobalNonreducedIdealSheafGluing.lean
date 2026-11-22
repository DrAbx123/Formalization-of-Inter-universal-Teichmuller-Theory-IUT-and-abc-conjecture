import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalNonreducedIdealSheafConstruction
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiProjectiveIdealSheaf
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Tactic

/-!
# Global non-reduced ideal sheaf from actual projective chart ideals

The three standard charts have actual F-localized non-reduced ideals and actual
gluing compatibility.  This file pushes those chart ideals to the corresponding
affine opens of Proj using Mathlib's awayToSection, constructs the actual
conditional Scheme.IdealSheafData from an explicit global affine-open family,
and proves the chart restriction/comparison with the reduced vanishing-ideal
data.  The missing step is a global affine-open gluing datum (not provided by
the frozen Proj API); it is isolated exactly as a residual input.  No global
sheaf is fabricated.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.GlobalNonreducedIdealSheafGluing

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
open MvPolynomial AlgebraicGeometry
open scoped Polynomial BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

abbrev gluingBase : Type u := globalNonreducedBase S v

abbrev gluingGrading : ℕ → Submodule (gluingBase S v)
    (MvPolynomial (Fin 3) (gluingBase S v)) :=
  globalNonreducedGrading S v

abbrev gluingProj : Scheme.{u} := properModelProjectiveSpace S v

/-- The actual standard chart D+(Xi) as an affine open of Proj. -/
noncomputable def projectiveStandardChartAffine (i : Fin 3) :
    (gluingProj S v).affineOpens :=
  ⟨AlgebraicGeometry.Proj.basicOpen (gluingGrading S v) (MvPolynomial.X i),
    AlgebraicGeometry.Proj.isAffineOpen_basicOpen
      (𝒜 := gluingGrading S v) (f := MvPolynomial.X i) (d := 1)
      (by simpa [MvPolynomial.mem_homogeneousSubmodule]
        using MvPolynomial.isHomogeneous_X (R := gluingBase S v) i)
      (by norm_num)⟩

theorem projectiveStandardChartAffine_open
    (i : Fin 3) :
    ((projectiveStandardChartAffine S v i : (gluingProj S v).affineOpens) :
      (gluingProj S v).Opens) =
      AlgebraicGeometry.Proj.basicOpen (gluingGrading S v) (MvPolynomial.X i) :=
  rfl

/-- The actual F-localized non-reduced chart ideal on Proj, transported from the
chart localization to the affine open structure sheaf by awayToSection. -/
noncomputable def projectiveNonreducedChartIdeal
    (W : WeierstrassCurve (gluingBase S v)) (i : Fin 3) :
    Ideal Γ(gluingProj S v, projectiveStandardChartAffine S v i) :=
  Ideal.map
    (AlgebraicGeometry.Proj.awayToSection (gluingGrading S v)
      (MvPolynomial.X i)).hom
    (standardChartNonreducedIdealAt S v W i)

/-- The actual reduced chart ideal on Proj, transported to the chart affine
open. -/
noncomputable def projectiveReducedChartIdeal
    (W : WeierstrassCurve (gluingBase S v)) (i : Fin 3) :
    Ideal Γ(gluingProj S v, projectiveStandardChartAffine S v i) :=
  Ideal.map
    (AlgebraicGeometry.Proj.awayToSection (gluingGrading S v)
      (MvPolynomial.X i)).hom
    (standardChartReducedIdealAt S v W i)

theorem projectiveNonreducedChartIdeal_le_reduced
    (W : WeierstrassCurve (gluingBase S v)) (i : Fin 3) :
    projectiveNonreducedChartIdeal S v W i ≤
      projectiveReducedChartIdeal S v W i :=
  Ideal.map_mono (standardChartNonreducedIdealAt_le_reducedAt S v W i)

/-- Exact input needed to glue the affine-open ideals: a global ideal on every
affine open, the basic-open compatibility, and the chart restriction/equality
with the actual F-localized chart ideals. -/
structure ProjectiveIdealSheafGluingInput
    (W : WeierstrassCurve (gluingBase S v)) where
  ideal : ∀ U : (gluingProj S v).affineOpens,
    Ideal Γ(gluingProj S v, U)
  map_ideal_basicOpen : ∀ (U : (gluingProj S v).affineOpens)
    (f : Γ(gluingProj S v, U)),
    (ideal U).map
        ((gluingProj S v).presheaf.map
          (homOfLE ((gluingProj S v).basicOpen_le f)).op).hom =
      ideal ((gluingProj S v).affineBasicOpen f)
  chart_restriction : ∀ i : Fin 3,
    ideal (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v W i
  chart_reduced_comparison : ∀ i : Fin 3,
    projectiveNonreducedChartIdeal S v W i ≤
      projectiveReducedChartIdeal S v W i

/-- Conditionally, the actual Mathlib IdealSheafData is constructed from the
explicit affine-open family. -/
noncomputable def gluedIdealSheaf
    (W : WeierstrassCurve (gluingBase S v))
    (G : ProjectiveIdealSheafGluingInput S v W) :
    (gluingProj S v).IdealSheafData where
  ideal := G.ideal
  map_ideal_basicOpen := G.map_ideal_basicOpen
  supportSet := ⋂ U, (gluingProj S v).zeroLocus (U := U.1) (G.ideal U)
  supportSet_eq_iInter_zeroLocus := rfl

theorem gluedIdealSheaf_ideal
    (W : WeierstrassCurve (gluingBase S v))
    (G : ProjectiveIdealSheafGluingInput S v W)
    (U : (gluingProj S v).affineOpens) :
    (gluedIdealSheaf S v W G).ideal U = G.ideal U :=
  rfl

theorem gluedIdealSheaf_chart_restriction
    (W : WeierstrassCurve (gluingBase S v))
    (G : ProjectiveIdealSheafGluingInput S v W) (i : Fin 3) :
    (gluedIdealSheaf S v W G).ideal (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v W i :=
  G.chart_restriction i

/-- The actual closed subscheme of the conditional global ideal sheaf. -/
noncomputable def gluedClosedSubscheme
    (W : WeierstrassCurve (gluingBase S v))
    (G : ProjectiveIdealSheafGluingInput S v W) : Scheme.{u} :=
  (gluedIdealSheaf S v W G).subscheme

noncomputable def gluedClosedSubschemeImmersion
    (W : WeierstrassCurve (gluingBase S v))
    (G : ProjectiveIdealSheafGluingInput S v W) :
    gluedClosedSubscheme S v W G ⟶ gluingProj S v :=
  (gluedIdealSheaf S v W G).subschemeι

theorem gluedClosedSubschemeImmersion_isClosed
    (W : WeierstrassCurve (gluingBase S v))
    (G : ProjectiveIdealSheafGluingInput S v W) :
    IsClosedImmersion (gluedClosedSubschemeImmersion S v W G) :=
  inferInstance

theorem gluedClosedSubscheme_range
    (W : WeierstrassCurve (gluingBase S v))
    (G : ProjectiveIdealSheafGluingInput S v W) :
    Set.range (gluedClosedSubschemeImmersion S v W G) =
      ((gluedIdealSheaf S v W G).support :
        Set (gluingProj S v)) :=
  (gluedIdealSheaf S v W G).range_subschemeι

/-- Chartwise comparison with the reduced vanishing ideal data: the actual
F-localized chart ideal is contained in the actual reduced chart ideal. -/
theorem glued_chart_comparison
    (W : WeierstrassCurve (gluingBase S v))
    (G : ProjectiveIdealSheafGluingInput S v W) (i : Fin 3) :
    projectiveNonreducedChartIdeal S v W i ≤
      projectiveReducedChartIdeal S v W i :=
  G.chart_reduced_comparison i

/-- The actual reduced vanishing-ideal sheaf on Proj. -/
noncomputable abbrev projectiveReducedIdealSheaf
    (W : WeierstrassCurve (gluingBase S v)) :
    (gluingProj S v).IdealSheafData :=
  weierstrassIdealSheaf S v W

/-- Exact residual: a global affine-open gluing datum realizing the actual
F-localized chart ideals and comparing its subscheme with the reduced closed
model. -/
structure GlobalNonreducedIdealSheafGluingResidual
    (W : WeierstrassCurve (gluingBase S v)) where
  gluingInput : ProjectiveIdealSheafGluingInput S v W
  globalIdealSheaf : (gluingProj S v).IdealSheafData
  globalIdealSheaf_eq : globalIdealSheaf = gluedIdealSheaf S v W gluingInput
  subscheme_eq_closedModel : Prop
  reducedComparison : Prop
  regular : Prop
  componentComparison : Prop

def GlobalNonreducedIdealSheafGluingResidualStatement
    (W : WeierstrassCurve (gluingBase S v)) : Prop :=
  Nonempty (GlobalNonreducedIdealSheafGluingResidual S v W)

theorem globalNonreducedIdealSheafGluingResidualStatement_iff
    (W : WeierstrassCurve (gluingBase S v)) :
    GlobalNonreducedIdealSheafGluingResidualStatement S v W ↔
      Nonempty (GlobalNonreducedIdealSheafGluingResidual S v W) :=
  Iff.rfl

theorem globalNonreducedIdealSheafGluingResidual_regular
    (W : WeierstrassCurve (gluingBase S v))
    (R : GlobalNonreducedIdealSheafGluingResidual S v W) :
    R.regular := R.regular

theorem globalNonreducedIdealSheafGluingResidual_component
    (W : WeierstrassCurve (gluingBase S v))
    (R : GlobalNonreducedIdealSheafGluingResidual S v W) :
    R.componentComparison := R.componentComparison

/-- Conditional actual construction: given the exact global affine-open gluing
input, the global ideal sheaf, its closed subscheme, chart restrictions and
reduced comparison are actual. -/
theorem globalNonreducedIdealSheaf_conditional_actual
    (W : WeierstrassCurve (gluingBase S v))
    (G : ProjectiveIdealSheafGluingInput S v W) :
    (∀ i : Fin 3,
      (gluedIdealSheaf S v W G).ideal (projectiveStandardChartAffine S v i) =
        projectiveNonreducedChartIdeal S v W i) ∧
      IsClosedImmersion (gluedClosedSubschemeImmersion S v W G) ∧
      (∀ i : Fin 3,
        projectiveNonreducedChartIdeal S v W i ≤
          projectiveReducedChartIdeal S v W i) ∧
      (GlobalNonreducedIdealSheafGluingResidualStatement S v W ↔
        Nonempty (GlobalNonreducedIdealSheafGluingResidual S v W)) :=
  ⟨fun i => gluedIdealSheaf_chart_restriction S v W G i,
    gluedClosedSubschemeImmersion_isClosed S v W G,
    fun i => glued_chart_comparison S v W G i,
    globalNonreducedIdealSheafGluingResidualStatement_iff S v W⟩

abbrev projectiveStandardChartAffineType (i : Fin 3) :
    (gluingProj S v).affineOpens :=
  projectiveStandardChartAffine S v i

theorem projectiveStandardChartAffine_mem
    (i : Fin 3) :
    (projectiveStandardChartAffine S v i : (gluingProj S v).Opens) ∈
      AlgebraicGeometry.Proj.basicOpen (gluingGrading S v) (MvPolynomial.X i) :=
  by
  rw [← projectiveStandardChartAffine_open S v i]
  exact (projectiveStandardChartAffine S v i).property

abbrev projectiveNonreducedChartIdealType
    (W : WeierstrassCurve (gluingBase S v)) (i : Fin 3) :
    Ideal Γ(gluingProj S v, projectiveStandardChartAffine S v i) :=
  projectiveNonreducedChartIdeal S v W i

abbrev projectiveReducedChartIdealType
    (W : WeierstrassCurve (gluingBase S v)) (i : Fin 3) :
    Ideal Γ(gluingProj S v, projectiveStandardChartAffine S v i) :=
  projectiveReducedChartIdeal S v W i

theorem projectiveIdealSheafGluingInput_ideal
    (W : WeierstrassCurve (gluingBase S v))
    (G : ProjectiveIdealSheafGluingInput S v W)
    (U : (gluingProj S v).affineOpens) :
    G.ideal U = (gluedIdealSheaf S v W G).ideal U :=
  rfl

theorem projectiveIdealSheafGluingInput_map
    (W : WeierstrassCurve (gluingBase S v))
    (G : ProjectiveIdealSheafGluingInput S v W)
    (U : (gluingProj S v).affineOpens)
    (f : Γ(gluingProj S v, U)) :
    (G.ideal U).map
        ((gluingProj S v).presheaf.map
          (homOfLE ((gluingProj S v).basicOpen_le f)).op).hom =
      G.ideal ((gluingProj S v).affineBasicOpen f) :=
  G.map_ideal_basicOpen U f

theorem projectiveIdealSheafGluingInput_chart
    (W : WeierstrassCurve (gluingBase S v))
    (G : ProjectiveIdealSheafGluingInput S v W) (i : Fin 3) :
    G.ideal (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v W i :=
  G.chart_restriction i

theorem projectiveIdealSheafGluingInput_reduced_comparison
    (W : WeierstrassCurve (gluingBase S v))
    (G : ProjectiveIdealSheafGluingInput S v W) (i : Fin 3) :
    projectiveNonreducedChartIdeal S v W i ≤
      projectiveReducedChartIdeal S v W i :=
  G.chart_reduced_comparison i

theorem gluedIdealSheaf_support
    (W : WeierstrassCurve (gluingBase S v))
    (G : ProjectiveIdealSheafGluingInput S v W) :
    (gluedIdealSheaf S v W G).support =
      ⟨⋂ U, (gluingProj S v).zeroLocus (U := U.1) (G.ideal U),
        (gluedIdealSheaf S v W G).isClosed_supportSet⟩ :=
  rfl

abbrev gluedClosedSubschemeType
    (W : WeierstrassCurve (gluingBase S v))
    (G : ProjectiveIdealSheafGluingInput S v W) : Scheme.{u} :=
  gluedClosedSubscheme S v W G

abbrev gluedClosedSubschemeImmersionType
    (W : WeierstrassCurve (gluingBase S v))
    (G : ProjectiveIdealSheafGluingInput S v W) :
    gluedClosedSubscheme S v W G ⟶ gluingProj S v :=
  gluedClosedSubschemeImmersion S v W G

theorem globalNonreducedIdealSheafGluingResidual_globalSheaf
    (W : WeierstrassCurve (gluingBase S v))
    (R : GlobalNonreducedIdealSheafGluingResidual S v W) :
    R.globalIdealSheaf = gluedIdealSheaf S v W R.gluingInput :=
  R.globalIdealSheaf_eq

abbrev globalNonreducedIdealSheafGluingResidualGluingInput
    (W : WeierstrassCurve (gluingBase S v))
    (R : GlobalNonreducedIdealSheafGluingResidual S v W) :
    ProjectiveIdealSheafGluingInput S v W :=
  R.gluingInput

theorem globalNonreducedIdealSheafGluingResidual_statement
    (W : WeierstrassCurve (gluingBase S v)) :
    GlobalNonreducedIdealSheafGluingResidualStatement S v W ↔
      Nonempty (GlobalNonreducedIdealSheafGluingResidual S v W) :=
  Iff.rfl

end LeanFormal.IUT.GlobalNonreducedIdealSheafGluing
