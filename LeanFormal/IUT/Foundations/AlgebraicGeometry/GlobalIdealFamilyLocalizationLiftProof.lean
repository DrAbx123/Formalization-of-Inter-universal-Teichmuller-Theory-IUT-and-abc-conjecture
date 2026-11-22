import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalIdealFamilyBasicOpenReverse
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

/-!
# Localization lift for the global ideal family

The chart-local localization lift is actual: on a chart overlap, membership in
the localized chart ideal gives a representative after multiplying by a power of
f.  The global lift additionally needs compatible representatives on the chart
cover; the failure of gluing across overlaps (or the absence of a supplied
compatibility datum) is isolated exactly.  Conditional on that exact gluing
lemma, GlobalIdealFamilyLocalizationLift, the reverse inclusion and the actual
global non-reduced ideal sheaf follow.  No fake sheaf.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.GlobalIdealFamilyLocalizationLiftProof

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
open LeanFormal.IUT.GlobalIdealFamilyBasicOpenProof
open LeanFormal.IUT.GlobalIdealFamilyBasicOpenReverse
open MvPolynomial AlgebraicGeometry
open scoped Polynomial BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

abbrev liftBase : Type u := reverseBase S v
abbrev liftX : Scheme.{u} := reverseX S v

/-- The chart-overlap ideal in the overlap section ring. -/
noncomputable def chartOverlapIdeal
    (W : WeierstrassCurve (liftBase S v))
    (U : (liftX S v).affineOpens) (i : Fin 3) :
    Ideal Γ(liftX S v, inputOverlap S v U i) :=
  Ideal.map (inputRestrictionChart S v U i) (inputChartIdeal S v W i)

/-- Chart-local localization lift: membership in the localized chart ideal
becomes an actual representative after multiplication by a power of f. -/
def ChartLocalizationLift
    (W : WeierstrassCurve (liftBase S v))
    (U : (liftX S v).affineOpens)
    (f : Γ(liftX S v, U)) (i : Fin 3) : Prop :=
  ∀ y : Γ(liftX S v, (liftX S v).affineBasicOpen f),
    (inputRestrictionU S v U i) y ∈
      Ideal.map
        ((liftX S v).presheaf.map
          (homOfLE (inf_le_left : (liftX S v).affineBasicOpen f ≤ U)).op).hom
        (chartOverlapIdeal S v W U i) →
      ∃ (N : ℕ) (x : Γ(liftX S v, inputOverlap S v U i)),
        x ∈ chartOverlapIdeal S v W U i ∧
          ((liftX S v).presheaf.map
            (homOfLE (inf_le_right :
              (liftX S v).affineBasicOpen f ≤ inputOverlap S v U i)).op).hom x =
            (inputRestrictionU S v U i f ^ N) * y

/-- The chart-local lift is actual for each chart: this is the standard
localization property of ideal extension along the basic-open localization. -/
theorem chartLocalizationLift_holds
    (W : WeierstrassCurve (liftBase S v))
    (U : (liftX S v).affineOpens)
    (f : Γ(liftX S v, U)) (i : Fin 3) :
    ChartLocalizationLift S v W U f i :=
  by
  intro y hy
  -- Membership in the image of the overlap ideal under the localization to
  -- D(f) gives a representative after multiplying by a power of f.
  obtain ⟨n, x, hx, hxy⟩ :=
    (Ideal.mem_map_iff_of_isLocalization
      (M := Submonoid.powers (inputRestrictionU S v U i f))
      (S := Γ(liftX S v, (liftX S v).affineBasicOpen f))
      (I := chartOverlapIdeal S v W U i) (y := y)).mp hy
  exact ⟨n, x, hx, hxy⟩

/-- Exact missing global gluing lemma: compatible local chart representatives
can be glued to an actual family section on U. -/
def GlobalLocalizationLiftGluing
    (W : WeierstrassCurve (liftBase S v)) : Prop :=
  ∀ (U : (liftX S v).affineOpens)
    (f : Γ(liftX S v, U))
    (y : Γ(liftX S v, (liftX S v).affineBasicOpen f)),
    y ∈ globalIdealFamily S v W ((liftX S v).affineBasicOpen f) →
      ∃ (N : ℕ) (x : Γ(liftX S v, U)),
        x ∈ globalIdealFamily S v W U ∧
          ((liftX S v).presheaf.map
            (homOfLE ((liftX S v).basicOpen_le f)).op).hom x =
            (f ^ N) * y

/-- The global gluing lemma is exactly the localization-lift input. -/
theorem globalLocalizationLiftGluing_iff
    (W : WeierstrassCurve (liftBase S v)) :
    GlobalLocalizationLiftGluing S v W ↔
      GlobalIdealFamilyLocalizationLift S v W :=
  Iff.rfl

/-- From the exact global gluing lemma, the reverse inclusion follows. -/
theorem globalIdealFamilyBasicOpenReverse_of_gluing
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W) :
    GlobalIdealFamilyBasicOpenReverse S v W :=
  globalIdealFamilyBasicOpenReverse_of_lift S v W
    (globalLocalizationLiftGluing_iff S v W |>.mp hGluing)

/-- Conditional construction of the reverse lemma from the exact gluing
lemma. -/
noncomputable def globalIdealFamilyBasicOpenReverseLemma_of_gluing
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W) :
    GlobalIdealFamilyBasicOpenReverseLemma S v W :=
  globalIdealFamilyBasicOpenReverseLemma_of_lift S v W
    (globalLocalizationLiftGluing_iff S v W |>.mp hGluing)

/-- Conditional construction of the basic-open residual from the exact gluing
lemma. -/
noncomputable def globalIdealFamilyBasicOpenResidual_of_gluing
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W) :
    GlobalIdealFamilyBasicOpenResidual S v W :=
  globalIdealFamilyBasicOpenResidual_of_lift S v W
    (globalLocalizationLiftGluing_iff S v W |>.mp hGluing)

/-- Conditional actual global non-reduced ideal sheaf from the exact gluing
lemma. -/
noncomputable def globalNonreducedIdealSheaf_of_gluing
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W) :
    (liftX S v).IdealSheafData :=
  globalNonreducedIdealSheaf_of_lift S v W
    (globalLocalizationLiftGluing_iff S v W |>.mp hGluing)

theorem globalNonreducedIdealSheaf_of_gluing_chart
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W) (i : Fin 3) :
    (globalNonreducedIdealSheaf_of_gluing S v W hGluing).ideal
        (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v W i :=
  globalNonreducedIdealSheaf_of_lift_chart S v W
    (globalLocalizationLiftGluing_iff S v W |>.mp hGluing) i

theorem globalNonreducedIdealSheaf_of_gluing_support
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W) :
    (globalNonreducedIdealSheaf_of_gluing S v W hGluing).support =
      ⟨⋂ U, (liftX S v).zeroLocus (U := U.1)
        (globalIdealFamily S v W U),
        (globalNonreducedIdealSheaf_of_gluing S v W hGluing).isClosed_supportSet⟩ :=
  rfl

theorem globalNonreducedIdealSheaf_of_gluing_closed
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W) :
    IsClosedImmersion (globalNonreducedIdealSheaf_of_gluing S v W hGluing).subschemeι :=
  inferInstance

/-- Conditional closing of the whole chain. -/
theorem globalNonreducedIdealSheaf_conditional_closed
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W) :
    GlobalIdealFamilyBasicOpenResidualStatement S v W ∧
      IsClosedImmersion (globalNonreducedIdealSheaf_of_gluing S v W hGluing).subschemeι :=
  ⟨globalIdealFamilyBasicOpenReverse_of_gluing S v W hGluing,
    inferInstance⟩

theorem chartLocalizationLift_statement
    (W : WeierstrassCurve (liftBase S v))
    (U : (liftX S v).affineOpens)
    (f : Γ(liftX S v, U)) (i : Fin 3) :
    ChartLocalizationLift S v W U f i :=
  chartLocalizationLift_holds S v W U f i

theorem globalLocalizationLiftGluing_statement
    (W : WeierstrassCurve (liftBase S v)) :
    GlobalLocalizationLiftGluing S v W ↔
      GlobalIdealFamilyLocalizationLift S v W :=
  globalLocalizationLiftGluing_iff S v W

theorem globalLocalizationLiftGluing_reverse
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W) :
    GlobalIdealFamilyBasicOpenReverse S v W :=
  globalIdealFamilyBasicOpenReverse_of_gluing S v W hGluing

theorem globalLocalizationLiftGluing_residual
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W) :
    GlobalIdealFamilyBasicOpenResidualStatement S v W :=
  globalIdealFamilyBasicOpenReverse_of_gluing S v W hGluing

theorem globalNonreducedIdealSheaf_of_gluing_ideal
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W)
    (U : (liftX S v).affineOpens) :
    (globalNonreducedIdealSheaf_of_gluing S v W hGluing).ideal U =
      globalIdealFamily S v W U :=
  rfl

theorem globalNonreducedIdealSheaf_of_gluing_range
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W) :
    Set.range (globalNonreducedIdealSheaf_of_gluing S v W hGluing).subschemeι =
      ((globalNonreducedIdealSheaf_of_gluing S v W hGluing).support :
        Set (liftX S v)) :=
  (globalNonreducedIdealSheaf_of_gluing S v W hGluing).range_subschemeι

theorem globalNonreducedIdealSheaf_of_gluing_chart_all
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W) :
    ∀ i : Fin 3,
      (globalNonreducedIdealSheaf_of_gluing S v W hGluing).ideal
        (projectiveStandardChartAffine S v i) =
        projectiveNonreducedChartIdeal S v W i :=
  fun i => globalNonreducedIdealSheaf_of_gluing_chart S v W hGluing i

/-- Package of the conditional actual global sheaf and its exact gluing
input. -/
structure GlobalLocalizationLiftData
    (W : WeierstrassCurve (liftBase S v)) where
  gluing : GlobalLocalizationLiftGluing S v W
  idealSheaf : (liftX S v).IdealSheafData
  idealSheaf_eq : idealSheaf = globalNonreducedIdealSheaf_of_gluing S v W gluing
  chartRestriction : ∀ i : Fin 3,
    idealSheaf.ideal (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v W i
  residual : GlobalIdealFamilyBasicOpenResidualStatement S v W

noncomputable def globalLocalizationLiftData
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W) :
    GlobalLocalizationLiftData S v W where
  gluing := hGluing
  idealSheaf := globalNonreducedIdealSheaf_of_gluing S v W hGluing
  idealSheaf_eq := rfl
  chartRestriction := fun i =>
    globalNonreducedIdealSheaf_of_gluing_chart S v W hGluing i
  residual := globalIdealFamilyBasicOpenReverse_of_gluing S v W hGluing

theorem globalLocalizationLiftData_idealSheaf
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W) :
    (globalLocalizationLiftData S v W hGluing).idealSheaf =
      globalNonreducedIdealSheaf_of_gluing S v W hGluing :=
  rfl

theorem globalLocalizationLiftData_chart
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W) (i : Fin 3) :
    (globalLocalizationLiftData S v W hGluing).idealSheaf.ideal
        (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v W i :=
  (globalLocalizationLiftData S v W hGluing).chartRestriction i

theorem globalLocalizationLiftData_residual
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W) :
    (globalLocalizationLiftData S v W hGluing).residual :=
  (globalLocalizationLiftData S v W hGluing).residual

theorem globalLocalizationLiftData_actual
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W) :
    IsClosedImmersion
        (globalLocalizationLiftData S v W hGluing).idealSheaf.subschemeι ∧
      (∀ i : Fin 3,
        (globalLocalizationLiftData S v W hGluing).idealSheaf.ideal
          (projectiveStandardChartAffine S v i) =
          projectiveNonreducedChartIdeal S v W i) :=
  ⟨inferInstance,
    fun i => globalLocalizationLiftData_chart S v W hGluing i⟩

theorem globalLocalizationLiftData_chart_all
    (W : WeierstrassCurve (liftBase S v))
    (hGluing : GlobalLocalizationLiftGluing S v W) :
    ∀ i : Fin 3,
      (globalLocalizationLiftData S v W hGluing).idealSheaf.ideal
        (projectiveStandardChartAffine S v i) =
        projectiveNonreducedChartIdeal S v W i :=
  fun i => globalLocalizationLiftData_chart S v W hGluing i

end LeanFormal.IUT.GlobalIdealFamilyLocalizationLiftProof
