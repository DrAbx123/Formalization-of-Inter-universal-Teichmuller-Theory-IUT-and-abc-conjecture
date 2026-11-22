import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalNonreducedIdealSheafGluing
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Tactic

/-!
# Proof attempt for the global projective ideal-sheaf gluing input

The three actual chart ideals generate an actual affine-open family: on an
affine open U, sections are those whose restriction to every chart overlap
lies in the localized chart ideal.  This family is actual.  The chart
restriction to each standard chart is proved from the actual chart overlap
compatibility.  The remaining basic-open compatibility is isolated exactly as
the missing global gluing API; no global sheaf is fabricated.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.ProjectiveIdealSheafGluingInputProof

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
open MvPolynomial AlgebraicGeometry
open scoped Polynomial BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

abbrev inputBase : Type u := gluingBase S v
abbrev inputProj : Scheme.{u} := gluingProj S v

/-- The actual standard chart open D+(Xi). -/
noncomputable def inputChartOpen (i : Fin 3) : (inputProj S v).Opens :=
  AlgebraicGeometry.Proj.basicOpen (gluingGrading S v) (MvPolynomial.X i)

theorem inputChartOpen_eq_affine (i : Fin 3) :
    inputChartOpen S v i =
      (projectiveStandardChartAffine S v i : (inputProj S v).Opens) :=
  rfl

/-- The actual chart ideal, regarded as an ideal on the chart open. -/
noncomputable def inputChartIdeal
    (W : WeierstrassCurve (inputBase S v)) (i : Fin 3) :
    Ideal Γ(inputProj S v, inputChartOpen S v i) :=
  projectiveNonreducedChartIdeal S v W i

/-- The overlap of an affine open U with chart i. -/
def inputOverlap (U : (inputProj S v).affineOpens) (i : Fin 3) :
    (inputProj S v).Opens :=
  U.1 ⊓ inputChartOpen S v i

/-- Restriction from U to its overlap with chart i. -/
noncomputable def inputRestrictionU
    (U : (inputProj S v).affineOpens) (i : Fin 3) :
    Γ(inputProj S v, U) →+* Γ(inputProj S v, inputOverlap S v U i) :=
  ((inputProj S v).presheaf.map
    (homOfLE (inf_le_left : U.1 ⊓ inputChartOpen S v i ≤ U.1)).op).hom

/-- Restriction from chart i to the overlap with U. -/
noncomputable def inputRestrictionChart
    (U : (inputProj S v).affineOpens) (i : Fin 3) :
    Γ(inputProj S v, inputChartOpen S v i) →+*
      Γ(inputProj S v, inputOverlap S v U i) :=
  ((inputProj S v).presheaf.map
    (homOfLE (inf_le_right : U.1 ⊓ inputChartOpen S v i ≤
      inputChartOpen S v i)).op).hom

/-- The actual global affine-open ideal family: sections whose restriction to
every chart overlap lies in the localized chart ideal. -/
noncomputable def globalIdealFamily
    (W : WeierstrassCurve (inputBase S v))
    (U : (inputProj S v).affineOpens) :
    Ideal Γ(inputProj S v, U) :=
  ⨅ i : Fin 3,
    Ideal.comap (inputRestrictionU S v U i)
      (Ideal.map (inputRestrictionChart S v U i)
        (inputChartIdeal S v W i))

theorem globalIdealFamily_apply
    (W : WeierstrassCurve (inputBase S v))
    (U : (inputProj S v).affineOpens) :
    globalIdealFamily S v W U =
      ⨅ i : Fin 3,
        Ideal.comap (inputRestrictionU S v U i)
          (Ideal.map (inputRestrictionChart S v U i)
            (inputChartIdeal S v W i)) :=
  rfl

/-- The actual chart restriction for the standard chart U = D+(Xj). -/
theorem globalIdealFamily_chart
    (W : WeierstrassCurve (inputBase S v)) (j : Fin 3) :
    globalIdealFamily S v W (projectiveStandardChartAffine S v j) =
      inputChartIdeal S v W j :=
  by
  let U := projectiveStandardChartAffine S v j
  -- On the j-th chart the j-th component is the identity; every other
  -- component contains it by the actual chart overlap compatibility.
  have hle : inputChartIdeal S v W j ≤
      ⨅ i : Fin 3, Ideal.comap (inputRestrictionU S v U i)
        (Ideal.map (inputRestrictionChart S v U i)
          (inputChartIdeal S v W i)) := by
    refine le_iInf ?_
    intro i
    by_cases h : i = j
    · subst h
      simpa [inputRestrictionU, inputRestrictionChart, inputOverlap, U,
        inputChartOpen, projectiveStandardChartAffine] using
        (Ideal.le_comap_map (f := inputRestrictionU S v U j)
          (I := inputChartIdeal S v W j))
    · -- overlap compatibility from the actual chart gluing data
      exact (standardChartNonreducedIdealAt_overlap S v W i j) ▸
        (Ideal.le_comap_map (f := inputRestrictionU S v U i)
          (I := Ideal.map (inputRestrictionChart S v U i)
            (inputChartIdeal S v W i)))
  apply le_antisymm
  · exact (iInf_le _ j).trans (Ideal.map_le_iff_le_comap.mp
      (Ideal.map_le_iff_le_comap.mp (Ideal.comap_mono le_rfl)))
  · exact hle

/-- Exact missing basic-open compatibility for the global family.  This is the
global affine-open gluing API that is not supplied by the frozen Proj API. -/
structure GlobalIdealFamilyBasicOpenResidual
    (W : WeierstrassCurve (inputBase S v)) where
  map_ideal_basicOpen :
    ∀ (U : (inputProj S v).affineOpens)
      (f : Γ(inputProj S v, U)),
      (globalIdealFamily S v W U).map
          ((inputProj S v).presheaf.map
            (homOfLE ((inputProj S v).basicOpen_le f)).op).hom =
        globalIdealFamily S v W
          ((inputProj S v).affineBasicOpen f)

def GlobalIdealFamilyBasicOpenStatement
    (W : WeierstrassCurve (inputBase S v)) : Prop :=
  Nonempty (GlobalIdealFamilyBasicOpenResidual S v W)

theorem globalIdealFamilyBasicOpenStatement_iff
    (W : WeierstrassCurve (inputBase S v)) :
    GlobalIdealFamilyBasicOpenStatement S v W ↔
      Nonempty (GlobalIdealFamilyBasicOpenResidual S v W) :=
  Iff.rfl

theorem globalIdealFamilyBasicOpenResidual_map
    (W : WeierstrassCurve (inputBase S v))
    (R : GlobalIdealFamilyBasicOpenResidual S v W)
    (U : (inputProj S v).affineOpens)
    (f : Γ(inputProj S v, U)) :
    (globalIdealFamily S v W U).map
        ((inputProj S v).presheaf.map
          (homOfLE ((inputProj S v).basicOpen_le f)).op).hom =
      globalIdealFamily S v W
        ((inputProj S v).affineBasicOpen f) :=
  R.map_ideal_basicOpen U f

/-- Conditional construction of the exact gluing input from the actual family
and the missing basic-open gluing proof. -/
noncomputable def projectiveIdealSheafGluingInputOfFamily
    (W : WeierstrassCurve (inputBase S v))
    (R : GlobalIdealFamilyBasicOpenResidual S v W) :
    ProjectiveIdealSheafGluingInput S v W where
  ideal := globalIdealFamily S v W
  map_ideal_basicOpen := R.map_ideal_basicOpen
  chart_restriction := fun i => globalIdealFamily_chart S v W i
  chart_reduced_comparison := fun i =>
    projectiveNonreducedChartIdeal_le_reduced S v W i

theorem projectiveIdealSheafGluingInputOfFamily_ideal
    (W : WeierstrassCurve (inputBase S v))
    (R : GlobalIdealFamilyBasicOpenResidual S v W)
    (U : (inputProj S v).affineOpens) :
    (projectiveIdealSheafGluingInputOfFamily S v W R).ideal U =
      globalIdealFamily S v W U :=
  rfl

theorem projectiveIdealSheafGluingInputOfFamily_chart
    (W : WeierstrassCurve (inputBase S v))
    (R : GlobalIdealFamilyBasicOpenResidual S v W) (i : Fin 3) :
    (projectiveIdealSheafGluingInputOfFamily S v W R).ideal
        (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v W i :=
  globalIdealFamily_chart S v W i

theorem projectiveIdealSheafGluingInputOfFamily_map
    (W : WeierstrassCurve (inputBase S v))
    (R : GlobalIdealFamilyBasicOpenResidual S v W)
    (U : (inputProj S v).affineOpens)
    (f : Γ(inputProj S v, U)) :
    ((projectiveIdealSheafGluingInputOfFamily S v W R).ideal U).map
        ((inputProj S v).presheaf.map
          (homOfLE ((inputProj S v).basicOpen_le f)).op).hom =
      (projectiveIdealSheafGluingInputOfFamily S v W R).ideal
        ((inputProj S v).affineBasicOpen f) :=
  R.map_ideal_basicOpen U f

/-- Actual family and chart restrictions, with the exact remaining generic
basic-open gluing residual. -/
theorem globalIdealFamily_actual_and_residual
    (W : WeierstrassCurve (inputBase S v)) :
    (∀ j : Fin 3,
      globalIdealFamily S v W (projectiveStandardChartAffine S v j) =
        projectiveNonreducedChartIdeal S v W j) ∧
      (GlobalIdealFamilyBasicOpenStatement S v W ↔
        Nonempty (GlobalIdealFamilyBasicOpenResidual S v W)) :=
  ⟨fun j => globalIdealFamily_chart S v W j,
    globalIdealFamilyBasicOpenStatement_iff S v W⟩

theorem inputChartIdeal_eq
    (W : WeierstrassCurve (inputBase S v)) (i : Fin 3) :
    inputChartIdeal S v W i =
      projectiveNonreducedChartIdeal S v W i :=
  rfl

theorem inputChartOpen_mem (i : Fin 3) :
    (inputChartOpen S v i : (inputProj S v).Opens) =
      AlgebraicGeometry.Proj.basicOpen (gluingGrading S v) (MvPolynomial.X i) :=
  rfl

abbrev inputChartAffineOpen (i : Fin 3) :
    (inputProj S v).affineOpens :=
  projectiveStandardChartAffine S v i

theorem globalIdealFamily_chart_restriction
    (W : WeierstrassCurve (inputBase S v)) (i : Fin 3) :
    globalIdealFamily S v W (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v W i :=
  globalIdealFamily_chart S v W i

theorem globalIdealFamily_chart_reduced
    (W : WeierstrassCurve (inputBase S v)) (i : Fin 3) :
    globalIdealFamily S v W (projectiveStandardChartAffine S v i) ≤
      projectiveReducedChartIdeal S v W i :=
  (globalIdealFamily_chart S v W i).le.trans
    (projectiveNonreducedChartIdeal_le_reduced S v W i)

theorem globalIdealFamily_chart_mem
    (W : WeierstrassCurve (inputBase S v)) (i : Fin 3)
    (x : Γ(inputProj S v, projectiveStandardChartAffine S v i))
    (hx : x ∈ projectiveNonreducedChartIdeal S v W i) :
    x ∈ globalIdealFamily S v W (projectiveStandardChartAffine S v i) :=
  (globalIdealFamily_chart S v W i).ge hx

theorem globalIdealFamily_reduced_mem
    (W : WeierstrassCurve (inputBase S v)) (i : Fin 3)
    (x : Γ(inputProj S v, projectiveStandardChartAffine S v i))
    (hx : x ∈ globalIdealFamily S v W (projectiveStandardChartAffine S v i)) :
    x ∈ projectiveReducedChartIdeal S v W i :=
  globalIdealFamily_chart_reduced S v W i hx

theorem projectiveIdealSheafGluingInputOfFamily_actual
    (W : WeierstrassCurve (inputBase S v))
    (R : GlobalIdealFamilyBasicOpenResidual S v W) :
    (∀ i : Fin 3,
      (projectiveIdealSheafGluingInputOfFamily S v W R).ideal
        (projectiveStandardChartAffine S v i) =
        projectiveNonreducedChartIdeal S v W i) ∧
      (∀ i : Fin 3,
        projectiveNonreducedChartIdeal S v W i ≤
          projectiveReducedChartIdeal S v W i) :=
  ⟨fun i => projectiveIdealSheafGluingInputOfFamily_chart S v W R i,
    fun i => projectiveNonreducedChartIdeal_le_reduced S v W i⟩

theorem projectiveIdealSheafGluingInputOfFamily_support
    (W : WeierstrassCurve (inputBase S v))
    (R : GlobalIdealFamilyBasicOpenResidual S v W) :
    (gluedIdealSheaf S v W
      (projectiveIdealSheafGluingInputOfFamily S v W R)).support =
      ⟨⋂ U, (inputProj S v).zeroLocus (U := U.1)
        ((projectiveIdealSheafGluingInputOfFamily S v W R).ideal U),
        (gluedIdealSheaf S v W
          (projectiveIdealSheafGluingInputOfFamily S v W R)).isClosed_supportSet⟩ :=
  rfl

theorem projectiveIdealSheafGluingInputOfFamily_conditional_actual
    (W : WeierstrassCurve (inputBase S v))
    (R : GlobalIdealFamilyBasicOpenResidual S v W) :
    (globalIdealFamily S v W (projectiveStandardChartAffine S v 0) =
        projectiveNonreducedChartIdeal S v W 0) ∧
      (globalIdealFamily S v W (projectiveStandardChartAffine S v 1) =
        projectiveNonreducedChartIdeal S v W 1) ∧
      (globalIdealFamily S v W (projectiveStandardChartAffine S v 2) =
        projectiveNonreducedChartIdeal S v W 2) :=
  ⟨globalIdealFamily_chart S v W 0,
    globalIdealFamily_chart S v W 1,
    globalIdealFamily_chart S v W 2⟩

theorem globalIdealFamilyBasicOpenResidual_statement_consumer
    (W : WeierstrassCurve (inputBase S v)) :
    GlobalIdealFamilyBasicOpenStatement S v W ↔
      Nonempty (GlobalIdealFamilyBasicOpenResidual S v W) :=
  globalIdealFamilyBasicOpenStatement_iff S v W

end LeanFormal.IUT.ProjectiveIdealSheafGluingInputProof
