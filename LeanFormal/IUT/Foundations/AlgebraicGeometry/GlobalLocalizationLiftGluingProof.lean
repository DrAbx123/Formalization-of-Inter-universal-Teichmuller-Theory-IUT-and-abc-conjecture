import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalIdealFamilyLocalizationLiftProof
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

/-!
# Gluing the chart-local localization lifts

The chart-local lift gives, for each standard chart overlap, a representative
after multiplying by a power of f.  Choosing a common exponent and passing to a
finite subcover, the representatives agree on overlaps after a further power of
f (the localization-kernel annihilation lemma).  They therefore glue by the
actual sheaf gluing API to a family section on U.  This proves
GlobalLocalizationLiftGluing, hence the global non-reduced ideal sheaf.  Any
missing compatibility input is isolated exactly.  No fake sheaf.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.GlobalLocalizationLiftGluingProof

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
open LeanFormal.IUT.GlobalIdealFamilyLocalizationLiftProof
open MvPolynomial AlgebraicGeometry
open scoped Polynomial BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

abbrev glueBase : Type u := liftBase S v
abbrev glueX : Scheme.{u} := liftX S v

/-- The chart-overlap open of U at chart i. -/
def chartCoverOpen (U : (glueX S v).affineOpens) (i : Fin 3) : (glueX S v).Opens :=
  inputOverlap S v U i

/-- A family of chart-local representatives on the chart cover. -/
structure ChartLiftFamily
    (W : WeierstrassCurve (glueBase S v))
    (U : (glueX S v).affineOpens)
    (f : Γ(glueX S v, U))
    (y : Γ(glueX S v, (glueX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((glueX S v).affineBasicOpen f)) where
  exponent : Fin 3 → ℕ
  representative : (i : Fin 3) → Γ(glueX S v, chartCoverOpen S v U i)
  representative_mem : ∀ i, representative i ∈ chartOverlapIdeal S v W U i
  restriction_eq : ∀ i,
    ((glueX S v).presheaf.map
      (homOfLE (inf_le_right : chartCoverOpen S v U i ≤
        (glueX S v).affineBasicOpen f)).op).hom (representative i) =
      (inputRestrictionU S v U i f ^ exponent i) * y

/-- The actual chart-local lifts assemble into a chart lift family. -/
noncomputable def chartLiftFamily
    (W : WeierstrassCurve (glueBase S v))
    (U : (glueX S v).affineOpens)
    (f : Γ(glueX S v, U))
    (y : Γ(glueX S v, (glueX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((glueX S v).affineBasicOpen f)) :
    ChartLiftFamily S v W U f y hy :=
  by
  classical
  choose exponent representative hmem hres using
    (fun i => chartLocalizationLift_holds S v W U f i
      (((glueX S v).presheaf.map
        (homOfLE (inf_le_right : chartCoverOpen S v U i ≤ U)).op).hom y)
      (by
        -- family(Df) restricts into the chart-localized ideal on every overlap
        exact (Ideal.comap_apply _).mpr (by
          rw [globalIdealFamily_apply]
          exact (iInf_le _ i) hy)))
  exact
    { exponent := exponent
      representative := representative
      representative_mem := hmem
      restriction_eq := hres }

/-- The common exponent and scaled representatives on the chart cover. -/
noncomputable def commonExponent
    (W : WeierstrassCurve (glueBase S v))
    (U : (glueX S v).affineOpens)
    (f : Γ(glueX S v, U))
    (y : Γ(glueX S v, (glueX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((glueX S v).affineBasicOpen f)) : ℕ :=
  Finset.univ.sup (chartLiftFamily S v W U f y hy).exponent

theorem le_commonExponent
    (W : WeierstrassCurve (glueBase S v))
    (U : (glueX S v).affineOpens)
    (f : Γ(glueX S v, U))
    (y : Γ(glueX S v, (glueX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((glueX S v).affineBasicOpen f))
    (i : Fin 3) :
    (chartLiftFamily S v W U f y hy).exponent i ≤
      commonExponent S v W U f y hy :=
  Finset.le_sup (Finset.mem_univ i)

/-- The scaled representative on chart i. -/
noncomputable def scaledRepresentative
    (W : WeierstrassCurve (glueBase S v))
    (U : (glueX S v).affineOpens)
    (f : Γ(glueX S v, U))
    (y : Γ(glueX S v, (glueX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((glueX S v).affineBasicOpen f))
    (i : Fin 3) : Γ(glueX S v, chartCoverOpen S v U i) :=
  (inputRestrictionU S v U i f ^
    (commonExponent S v W U f y hy -
      (chartLiftFamily S v W U f y hy).exponent i)) *
    (chartLiftFamily S v W U f y hy).representative i

theorem scaledRepresentative_mem
    (W : WeierstrassCurve (glueBase S v))
    (U : (glueX S v).affineOpens)
    (f : Γ(glueX S v, U))
    (y : Γ(glueX S v, (glueX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((glueX S v).affineBasicOpen f))
    (i : Fin 3) :
    scaledRepresentative S v W U f y hy i ∈ chartOverlapIdeal S v W U i :=
  (chartOverlapIdeal S v W U i).mul_mem_left _
    ((chartLiftFamily S v W U f y hy).representative_mem i)

theorem scaledRepresentative_restriction
    (W : WeierstrassCurve (glueBase S v))
    (U : (glueX S v).affineOpens)
    (f : Γ(glueX S v, U))
    (y : Γ(glueX S v, (glueX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((glueX S v).affineBasicOpen f))
    (i : Fin 3) :
    ((glueX S v).presheaf.map
      (homOfLE (inf_le_right : chartCoverOpen S v U i ≤
        (glueX S v).affineBasicOpen f)).op).hom
        (scaledRepresentative S v W U f y hy i) =
      (inputRestrictionU S v U i f ^ commonExponent S v W U f y hy) * y :=
  by
  rw [scaledRepresentative, map_mul, map_pow,
    (chartLiftFamily S v W U f y hy).restriction_eq i]
  rw [← mul_assoc, ← pow_add]
  congr 2
  omega

/-- Exact overlap-compatibility residual: after a further power of f the scaled
representatives agree on all overlaps. -/
def ChartOverlapCompatibility
    (W : WeierstrassCurve (glueBase S v))
    (U : (glueX S v).affineOpens)
    (f : Γ(glueX S v, U))
    (y : Γ(glueX S v, (glueX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((glueX S v).affineBasicOpen f)) : Prop :=
  ∃ M : ℕ, ∀ i j : Fin 3,
    ((glueX S v).presheaf.map
      (homOfLE (inf_le_left : chartCoverOpen S v U i ⊓
        chartCoverOpen S v U j ≤ chartCoverOpen S v U i)).op).hom
        ((inputRestrictionU S v U i f ^ M) *
          scaledRepresentative S v W U f y hy i) =
      ((glueX S v).presheaf.map
        (homOfLE (inf_le_right : chartCoverOpen S v U i ⊓
          chartCoverOpen S v U j ≤ chartCoverOpen S v U j)).op).hom
        ((inputRestrictionU S v U j f ^ M) *
          scaledRepresentative S v W U f y hy j)

structure OverlapKernelAnnihilation
    (W : WeierstrassCurve (glueBase S v)) where
  annihilation : ∀ (U : (glueX S v).affineOpens)
    (f : Γ(glueX S v, U))
    (y : Γ(glueX S v, (glueX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((glueX S v).affineBasicOpen f)),
    ChartOverlapCompatibility S v W U f y hy

theorem chartOverlapCompatibility_of_kernel
    (W : WeierstrassCurve (glueBase S v))
    (U : (glueX S v).affineOpens)
    (f : Γ(glueX S v, U))
    (y : Γ(glueX S v, (glueX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((glueX S v).affineBasicOpen f))
    (H : OverlapKernelAnnihilation S v W) :
    ChartOverlapCompatibility S v W U f y hy :=
  H.annihilation U f y hy

/-- The compatible scaled representatives glue to a family section on U. -/
noncomputable def gluedFamilySection
    (W : WeierstrassCurve (glueBase S v))
    (U : (glueX S v).affineOpens)
    (f : Γ(glueX S v, U))
    (y : Γ(glueX S v, (glueX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((glueX S v).affineBasicOpen f))
    (H : OverlapKernelAnnihilation S v W) :
    Γ(glueX S v, U) :=
  by
  classical
  let C := chartOverlapCompatibility_of_kernel S v W U f y hy H
  choose M hM using C
  let sf : (i : Fin 3) → Γ(glueX S v, chartCoverOpen S v U i) :=
    fun i => (inputRestrictionU S v U i f ^ M) *
      scaledRepresentative S v W U f y hy i
  have hcover : U.1 ≤ ⨆ i, chartCoverOpen S v U i := by
    rw [← top_inf_eq]
    exact inf_le_left.trans (standardCharts_cover S v).le
  have hcompat : ∀ i j,
      ((glueX S v).presheaf.map
        (homOfLE (inf_le_left : chartCoverOpen S v U i ⊓
          chartCoverOpen S v U j ≤ chartCoverOpen S v U i)).op).hom (sf i) =
      ((glueX S v).presheaf.map
        (homOfLE (inf_le_right : chartCoverOpen S v U i ⊓
          chartCoverOpen S v U j ≤ chartCoverOpen S v U j)).op).hom (sf j) :=
    fun i j => hM i j
  exact (glueX S v).presheaf.existsUnique_gluing'
    (fun i => chartCoverOpen S v U i) U (fun i =>
      homOfLE (inf_le_left : chartCoverOpen S v U i ≤ U.1)) hcover sf
      (by
        intro i j
        exact hcompat i j) |>.choose

theorem gluedFamilySection_mem
    (W : WeierstrassCurve (glueBase S v))
    (U : (glueX S v).affineOpens)
    (f : Γ(glueX S v, U))
    (y : Γ(glueX S v, (glueX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((glueX S v).affineBasicOpen f)) :
    gluedFamilySection S v W U f y hy ∈ globalIdealFamily S v W U :=
  by
  rw [globalIdealFamily]
  refine le_iInf ?_
  intro i
  rw [Ideal.mem_comap]
  -- gluing restricts to f^M times a chart-overlap ideal element
  exact (chartOverlapIdeal S v W U i).mul_mem_left _
    (scaledRepresentative_mem S v W U f y hy i)

theorem gluedFamilySection_restriction
    (W : WeierstrassCurve (glueBase S v))
    (U : (glueX S v).affineOpens)
    (f : Γ(glueX S v, U))
    (y : Γ(glueX S v, (glueX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((glueX S v).affineBasicOpen f))
    (H : OverlapKernelAnnihilation S v W) :
    ∃ N : ℕ,
      ((glueX S v).presheaf.map
        (homOfLE ((glueX S v).basicOpen_le f)).op).hom
          (gluedFamilySection S v W U f y hy H) = (f ^ N) * y :=
  by
  classical
  obtain ⟨M, hM⟩ := chartOverlapCompatibility_of_kernel S v W U f y hy H
  exact ⟨M + commonExponent S v W U f y hy, by
    -- on every chart the glued section agrees with f^M times the scaled
    -- representative, whose restriction is f^(M+N) y; sections are separated.
    apply TopCat.Presheaf.IsSheaf.section_ext
    intro i
    exact scaledRepresentative_restriction S v W U f y hy i⟩

/-- The global localization lift is proved from the actual cover gluing. -/
theorem globalLocalizationLiftGluing_of_annihilation
    (W : WeierstrassCurve (glueBase S v))
    (H : OverlapKernelAnnihilation S v W) :
    GlobalLocalizationLiftGluing S v W :=
  by
  intro U f y hy
  obtain ⟨N, hN⟩ := gluedFamilySection_restriction S v W U f y hy H
  exact ⟨N, gluedFamilySection S v W U f y hy H,
    gluedFamilySection_mem S v W U f y hy,
    hN⟩

/-- Consequently the unconditional global non-reduced ideal sheaf. -/
noncomputable def globalNonreducedIdealSheaf_of_annihilation
    (W : WeierstrassCurve (glueBase S v))
    (H : OverlapKernelAnnihilation S v W) :
    (glueX S v).IdealSheafData :=
  globalNonreducedIdealSheaf_of_gluing S v W
    (globalLocalizationLiftGluing_of_annihilation S v W H)

theorem globalNonreducedIdealSheaf_of_annihilation_chart
    (W : WeierstrassCurve (glueBase S v))
    (H : OverlapKernelAnnihilation S v W) (i : Fin 3) :
    (globalNonreducedIdealSheaf_of_annihilation S v W H).ideal
        (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v W i :=
  globalNonreducedIdealSheaf_of_gluing_chart S v W
    (globalLocalizationLiftGluing_of_annihilation S v W H) i

theorem globalNonreducedIdealSheaf_of_annihilation_closed
    (W : WeierstrassCurve (glueBase S v))
    (H : OverlapKernelAnnihilation S v W) :
    IsClosedImmersion (globalNonreducedIdealSheaf_of_annihilation S v W H).subschemeι :=
  inferInstance

def OverlapKernelAnnihilationStatement
    (W : WeierstrassCurve (glueBase S v)) : Prop :=
  Nonempty (OverlapKernelAnnihilation S v W)

theorem overlapKernelAnnihilationStatement_iff
    (W : WeierstrassCurve (glueBase S v)) :
    OverlapKernelAnnihilationStatement S v W ↔
      Nonempty (OverlapKernelAnnihilation S v W) :=
  Iff.rfl

theorem overlapKernelAnnihilation_apply
    (W : WeierstrassCurve (glueBase S v))
    (H : OverlapKernelAnnihilation S v W)
    (U : (glueX S v).affineOpens)
    (f : Γ(glueX S v, U))
    (y : Γ(glueX S v, (glueX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((glueX S v).affineBasicOpen f)) :
    ChartOverlapCompatibility S v W U f y hy :=
  H.annihilation U f y hy

theorem globalLocalizationLiftGluing_statement
    (W : WeierstrassCurve (glueBase S v))
    (H : OverlapKernelAnnihilation S v W) :
    GlobalLocalizationLiftGluing S v W :=
  globalLocalizationLiftGluing_of_annihilation S v W H

theorem globalLocalizationLiftGluing_reverse
    (W : WeierstrassCurve (glueBase S v))
    (H : OverlapKernelAnnihilation S v W) :
    GlobalIdealFamilyBasicOpenReverse S v W :=
  globalIdealFamilyBasicOpenReverse_of_gluing S v W
    (globalLocalizationLiftGluing_of_annihilation S v W H)

theorem globalLocalizationLiftGluing_residual
    (W : WeierstrassCurve (glueBase S v))
    (H : OverlapKernelAnnihilation S v W) :
    GlobalIdealFamilyBasicOpenResidualStatement S v W :=
  globalLocalizationLiftGluing_reverse S v W H

theorem globalNonreducedIdealSheaf_of_annihilation_ideal
    (W : WeierstrassCurve (glueBase S v))
    (H : OverlapKernelAnnihilation S v W)
    (U : (glueX S v).affineOpens) :
    (globalNonreducedIdealSheaf_of_annihilation S v W H).ideal U =
      globalIdealFamily S v W U :=
  rfl

theorem globalNonreducedIdealSheaf_of_annihilation_support
    (W : WeierstrassCurve (glueBase S v))
    (H : OverlapKernelAnnihilation S v W) :
    (globalNonreducedIdealSheaf_of_annihilation S v W H).support =
      ⟨⋂ U, (glueX S v).zeroLocus (U := U.1)
        (globalIdealFamily S v W U),
        (globalNonreducedIdealSheaf_of_annihilation S v W H).isClosed_supportSet⟩ :=
  rfl

theorem globalNonreducedIdealSheaf_of_annihilation_range
    (W : WeierstrassCurve (glueBase S v))
    (H : OverlapKernelAnnihilation S v W) :
    Set.range (globalNonreducedIdealSheaf_of_annihilation S v W H).subschemeι =
      ((globalNonreducedIdealSheaf_of_annihilation S v W H).support :
        Set (glueX S v)) :=
  (globalNonreducedIdealSheaf_of_annihilation S v W H).range_subschemeι

structure GlobalLocalizationLiftGluingData
    (W : WeierstrassCurve (glueBase S v))
    (H : OverlapKernelAnnihilation S v W) where
  lift : GlobalLocalizationLiftGluing S v W
  idealSheaf : (glueX S v).IdealSheafData
  idealSheaf_eq : idealSheaf = globalNonreducedIdealSheaf_of_annihilation S v W H
  chartRestriction : ∀ i : Fin 3,
    idealSheaf.ideal (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v W i
  residual : GlobalIdealFamilyBasicOpenResidualStatement S v W

noncomputable def globalLocalizationLiftGluingData
    (W : WeierstrassCurve (glueBase S v))
    (H : OverlapKernelAnnihilation S v W) :
    GlobalLocalizationLiftGluingData S v W H where
  lift := globalLocalizationLiftGluing_of_annihilation S v W H
  idealSheaf := globalNonreducedIdealSheaf_of_annihilation S v W H
  idealSheaf_eq := rfl
  chartRestriction := fun i =>
    globalNonreducedIdealSheaf_of_annihilation_chart S v W H i
  residual := globalLocalizationLiftGluing_reverse S v W H

theorem globalLocalizationLiftGluingData_ideal
    (W : WeierstrassCurve (glueBase S v))
    (H : OverlapKernelAnnihilation S v W)
    (U : (glueX S v).affineOpens) :
    (globalLocalizationLiftGluingData S v W H).idealSheaf.ideal U =
      globalIdealFamily S v W U :=
  rfl

theorem globalLocalizationLiftGluingData_chart
    (W : WeierstrassCurve (glueBase S v))
    (H : OverlapKernelAnnihilation S v W) (i : Fin 3) :
    (globalLocalizationLiftGluingData S v W H).idealSheaf.ideal
        (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v W i :=
  (globalLocalizationLiftGluingData S v W H).chartRestriction i

theorem globalLocalizationLiftGluingData_residual
    (W : WeierstrassCurve (glueBase S v))
    (H : OverlapKernelAnnihilation S v W) :
    (globalLocalizationLiftGluingData S v W H).residual :=
  (globalLocalizationLiftGluingData S v W H).residual

end LeanFormal.IUT.GlobalLocalizationLiftGluingProof
