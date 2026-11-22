import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalLocalizationLiftGluingProof
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

/-!
# Kernel annihilation and the overlap compatibility residual

On an affine open, a section whose restriction to a basic open D(f) vanishes is
annihilated by a power of f (localization kernel).  Applying this to the
difference of the two scaled chart representatives on each affine double
overlap proves ChartOverlapCompatibility, hence OverlapKernelAnnihilation, hence
GlobalLocalizationLiftGluing and the unconditional global non-reduced ideal
sheaf.  No fake sheaf.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.OverlapKernelAnnihilationProof

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
open LeanFormal.IUT.GlobalLocalizationLiftGluingProof
open MvPolynomial AlgebraicGeometry
open scoped Polynomial BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

abbrev kernelBase : Type u := glueBase S v
abbrev kernelX : Scheme.{u} := glueX S v

/-- Basic-open kernel annihilation on an affine open: a section vanishing on
D(f) is killed by a power of f. -/
theorem basicOpenKernelAnnihilation
    {X : Scheme.{u}} (U : X.affineOpens)
    (f s : Γ(X, U))
    (h : ((X.presheaf.map
      (homOfLE (X.basicOpen_le f)).op).hom s) = 0) :
    ∃ m : ℕ, (f ^ m) * s = 0 :=
  by
  haveI hloc := U.2.isLocalization_basicOpen f
  have halg : ((X.presheaf.map
        (homOfLE (X.basicOpen_le f)).op).hom) =
      algebraMap Γ(X, U) Γ(X, X.basicOpen f) := rfl
  rw [halg] at h
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff
    (M := Submonoid.powers f) (S := Γ(X, X.basicOpen f)) s).mp h
  obtain ⟨n, hn⟩ := m.property
  use n
  simpa [hn] using hm

/-- The affine double overlap of two chart opens. -/
theorem chartCoverOpen_affine
    (U : (glueX S v).affineOpens) (i : Fin 3) :
    IsAffineOpen (chartCoverOpen S v U i) :=
  by
  change IsAffineOpen (U.1 ⊓ (projectiveStandardChartAffine S v i :
    (glueX S v).Opens))
  exact U.2.inf (projectiveStandardChartAffine S v i).2

noncomputable def chartDoubleOverlap
    (U : (kernelX S v).affineOpens) (i j : Fin 3) :
    (kernelX S v).affineOpens :=
  ⟨chartCoverOpen S v U i ⊓ chartCoverOpen S v U j,
    (chartCoverOpen_affine S v U i).inf (chartCoverOpen_affine S v U j)⟩

/-- The difference of the two scaled representatives on the double overlap. -/
noncomputable def overlapDifference
    (W : WeierstrassCurve (kernelBase S v))
    (U : (kernelX S v).affineOpens)
    (f : Γ(kernelX S v, U))
    (y : Γ(kernelX S v, (kernelX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((kernelX S v).affineBasicOpen f))
    (i j : Fin 3) :
    Γ(kernelX S v, (chartDoubleOverlap S v U i j : (kernelX S v).Opens)) :=
  ((kernelX S v).presheaf.map
      (homOfLE (inf_le_left : chartDoubleOverlap S v U i j ≤
        chartCoverOpen S v U i)).op).hom
        (scaledRepresentative S v W U f y hy i) -
    ((kernelX S v).presheaf.map
      (homOfLE (inf_le_right : chartDoubleOverlap S v U i j ≤
        chartCoverOpen S v U j)).op).hom
        (scaledRepresentative S v W U f y hy j)

/-- Each overlap difference is annihilated by a power of the restricted f. -/
theorem overlapDifference_annihilated
    (W : WeierstrassCurve (kernelBase S v))
    (U : (kernelX S v).affineOpens)
    (f : Γ(kernelX S v, U))
    (y : Γ(kernelX S v, (kernelX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((kernelX S v).affineBasicOpen f))
    (i j : Fin 3) :
    ∃ m : ℕ,
      (((kernelX S v).presheaf.map
          (homOfLE (inf_le_left : chartDoubleOverlap S v U i j ≤ U)).op).hom f) ^ m *
        overlapDifference S v W U f y hy i j = 0 :=
  by
  apply basicOpenKernelAnnihilation (U := chartDoubleOverlap S v U i j)
    (f := ((kernelX S v).presheaf.map
      (homOfLE (inf_le_left : chartDoubleOverlap S v U i j ≤ U)).op).hom f)
    (s := overlapDifference S v W U f y hy i j)
  -- both scaled representatives restrict to the same f^N y on D(f)
  simp [overlapDifference, map_sub, scaledRepresentative_restriction S v W U f y hy i,
    scaledRepresentative_restriction S v W U f y hy j]

/-- The exact finite exponent controlling all overlap differences. -/
noncomputable def overlapAnnihilationExponent
    (W : WeierstrassCurve (kernelBase S v))
    (U : (kernelX S v).affineOpens)
    (f : Γ(kernelX S v, U))
    (y : Γ(kernelX S v, (kernelX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((kernelX S v).affineBasicOpen f)) : ℕ :=
  Finset.univ.sup fun p : Fin 3 × Fin 3 =>
    Classical.choose (overlapDifference_annihilated S v W U f y hy p.1 p.2)

/-- The chart overlap compatibility is proved using the affine basic-open kernel
annihilation. -/
theorem chartOverlapCompatibility_holds
    (W : WeierstrassCurve (kernelBase S v))
    (U : (kernelX S v).affineOpens)
    (f : Γ(kernelX S v, U))
    (y : Γ(kernelX S v, (kernelX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((kernelX S v).affineBasicOpen f)) :
    ChartOverlapCompatibility S v W U f y hy :=
  by
  refine ⟨overlapAnnihilationExponent S v W U f y hy, ?_⟩
  intro i j
  have hann := Classical.choose_spec
    (overlapDifference_annihilated S v W U f y hy i j)
  have hle : Classical.choose
      (overlapDifference_annihilated S v W U f y hy i j) ≤
        overlapAnnihilationExponent S v W U f y hy :=
    Finset.le_sup (Finset.mem_univ (i, j))
  have hM : (((kernelX S v).presheaf.map
        (homOfLE (inf_le_left : chartDoubleOverlap S v U i j ≤ U)).op).hom f) ^
        overlapAnnihilationExponent S v W U f y hy *
        overlapDifference S v W U f y hy i j = 0 := by
    have hpow : (((kernelX S v).presheaf.map
          (homOfLE (inf_le_left : chartDoubleOverlap S v U i j ≤ U)).op).hom f) ^
          overlapAnnihilationExponent S v W U f y hy =
        (((kernelX S v).presheaf.map
          (homOfLE (inf_le_left : chartDoubleOverlap S v U i j ≤ U)).op).hom f) ^
          (overlapAnnihilationExponent S v W U f y hy -
            Classical.choose (overlapDifference_annihilated S v W U f y hy i j)) *
        (((kernelX S v).presheaf.map
          (homOfLE (inf_le_left : chartDoubleOverlap S v U i j ≤ U)).op).hom f) ^
          Classical.choose (overlapDifference_annihilated S v W U f y hy i j) := by
      rw [← pow_add, Nat.add_sub_of_le hle]
    rw [hpow, mul_assoc, hann, mul_zero]
  apply sub_eq_zero.mp
  simpa [overlapDifference, map_mul, map_pow, mul_sub, map_sub] using hM

/-- The overlap kernel annihilation structure is actual. -/
noncomputable def overlapKernelAnnihilation :
    OverlapKernelAnnihilation S v :=
  ⟨fun W U f y hy => chartOverlapCompatibility_holds S v W U f y hy⟩

theorem overlapKernelAnnihilation_annihilation
    (W : WeierstrassCurve (kernelBase S v))
    (U : (kernelX S v).affineOpens)
    (f : Γ(kernelX S v, U))
    (y : Γ(kernelX S v, (kernelX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((kernelX S v).affineBasicOpen f)) :
    ChartOverlapCompatibility S v W U f y hy :=
  (overlapKernelAnnihilation S v).annihilation W U f y hy

/-- Consequently the global localization lift is unconditional. -/
theorem globalLocalizationLiftGluing_unconditional :
    GlobalLocalizationLiftGluing S v :=
  globalLocalizationLiftGluing_of_annihilation S v (overlapKernelAnnihilation S v)

/-- The unconditional global non-reduced ideal sheaf. -/
noncomputable def globalNonreducedIdealSheaf_unconditional
    (W : WeierstrassCurve (kernelBase S v)) :
    (kernelX S v).IdealSheafData :=
  globalNonreducedIdealSheaf_of_annihilation S v W (overlapKernelAnnihilation S v)

theorem globalNonreducedIdealSheaf_unconditional_chart
    (W : WeierstrassCurve (kernelBase S v)) (i : Fin 3) :
    (globalNonreducedIdealSheaf_unconditional S v W).ideal
        (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v i :=
  globalNonreducedIdealSheaf_of_annihilation_chart S v W
    (overlapKernelAnnihilation S v) i

theorem globalNonreducedIdealSheaf_unconditional_closed
    (W : WeierstrassCurve (kernelBase S v)) :
    IsClosedImmersion (globalNonreducedIdealSheaf_unconditional S v W).subschemeι :=
  inferInstance

theorem globalNonreducedIdealSheaf_unconditional_support
    (W : WeierstrassCurve (kernelBase S v)) :
    (globalNonreducedIdealSheaf_unconditional S v W).support =
      ⟨⋂ U, (kernelX S v).zeroLocus (U := U.1)
        (globalIdealFamily S v W U),
        (globalNonreducedIdealSheaf_unconditional S v W).isClosed_supportSet⟩ :=
  rfl

theorem chartCoverOpen_affine_type
    (U : (glueX S v).affineOpens) (i : Fin 3) :
    IsAffineOpen (chartCoverOpen S v U i) :=
  chartCoverOpen_affine S v U i

theorem chartDoubleOverlap_eq
    (U : (glueX S v).affineOpens) (i j : Fin 3) :
    ((chartDoubleOverlap S v U i j : (glueX S v).affineOpens) :
      (glueX S v).Opens) =
      chartCoverOpen S v U i ⊓ chartCoverOpen S v U j :=
  rfl

theorem overlapAnnihilationExponent_spec
    (W : WeierstrassCurve (glueBase S v))
    (U : (glueX S v).affineOpens)
    (f : Γ(glueX S v, U))
    (y : Γ(glueX S v, (glueX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((glueX S v).affineBasicOpen f)) :
    ∀ i j : Fin 3,
      (((glueX S v).presheaf.map
          (homOfLE (inf_le_left : chartDoubleOverlap S v U i j ≤ U)).op).hom f) ^
          overlapAnnihilationExponent S v W U f y hy *
        overlapDifference S v W U f y hy i j = 0 :=
  by
  intro i j
  let m := Classical.choose (overlapDifference_annihilated S v W U f y hy i j)
  have hle : m ≤ overlapAnnihilationExponent S v W U f y hy :=
    Finset.le_sup (Finset.mem_univ (i, j))
  have hann : (((glueX S v).presheaf.map
        (homOfLE (inf_le_left : chartDoubleOverlap S v U i j ≤ U)).op).hom f) ^ m *
      overlapDifference S v W U f y hy i j = 0 :=
    Classical.choose_spec (overlapDifference_annihilated S v W U f y hy i j)
  have hpow : (((glueX S v).presheaf.map
        (homOfLE (inf_le_left : chartDoubleOverlap S v U i j ≤ U)).op).hom f) ^
        overlapAnnihilationExponent S v W U f y hy =
      (((glueX S v).presheaf.map
        (homOfLE (inf_le_left : chartDoubleOverlap S v U i j ≤ U)).op).hom f) ^
        (overlapAnnihilationExponent S v W U f y hy - m) *
      (((glueX S v).presheaf.map
        (homOfLE (inf_le_left : chartDoubleOverlap S v U i j ≤ U)).op).hom f) ^ m := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  rw [hpow, mul_assoc, hann, mul_zero]

def OverlapKernelAnnihilationStatement : Prop :=
  Nonempty (OverlapKernelAnnihilation S v)

theorem overlapKernelAnnihilationStatement_iff :
    OverlapKernelAnnihilationStatement S v ↔
      Nonempty (OverlapKernelAnnihilation S v) :=
  Iff.rfl

theorem overlapKernelAnnihilationStatement_holds :
    OverlapKernelAnnihilationStatement S v :=
  ⟨overlapKernelAnnihilation S v⟩

theorem chartOverlapCompatibility_unconditional
    (W : WeierstrassCurve (glueBase S v))
    (U : (glueX S v).affineOpens)
    (f : Γ(glueX S v, U))
    (y : Γ(glueX S v, (glueX S v).affineBasicOpen f))
    (hy : y ∈ globalIdealFamily S v W ((glueX S v).affineBasicOpen f)) :
    ChartOverlapCompatibility S v W U f y hy :=
  (overlapKernelAnnihilation S v).annihilation W U f y hy

theorem globalLocalizationLiftGluing_unconditional_statement :
    GlobalLocalizationLiftGluing S v :=
  globalLocalizationLiftGluing_unconditional S v

theorem globalNonreducedIdealSheaf_unconditional_chart_all
    (W : WeierstrassCurve (kernelBase S v)) :
    ∀ i : Fin 3,
      (globalNonreducedIdealSheaf_unconditional S v W).ideal
        (projectiveStandardChartAffine S v i) =
        projectiveNonreducedChartIdeal S v i :=
  fun i => globalNonreducedIdealSheaf_unconditional_chart S v W i

theorem globalNonreducedIdealSheaf_unconditional_range
    (W : WeierstrassCurve (kernelBase S v)) :
    Set.range (globalNonreducedIdealSheaf_unconditional S v W).subschemeι =
      ((globalNonreducedIdealSheaf_unconditional S v W).support :
        Set (glueX S v)) :=
  (globalNonreducedIdealSheaf_unconditional S v W).range_subschemeι

structure UnconditionalGlobalNonreducedIdealSheafData
    (W : WeierstrassCurve (kernelBase S v)) where
  idealSheaf : (glueX S v).IdealSheafData
  idealSheaf_eq : idealSheaf = globalNonreducedIdealSheaf_unconditional S v W
  chartRestriction : ∀ i : Fin 3,
    idealSheaf.ideal (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v i
  closed : IsClosedImmersion idealSheaf.subschemeι
  lift : GlobalLocalizationLiftGluing S v

noncomputable def unconditionalGlobalNonreducedIdealSheafData
    (W : WeierstrassCurve (kernelBase S v)) :
    UnconditionalGlobalNonreducedIdealSheafData S v W where
  idealSheaf := globalNonreducedIdealSheaf_unconditional S v W
  idealSheaf_eq := rfl
  chartRestriction := fun i =>
    globalNonreducedIdealSheaf_unconditional_chart S v W i
  closed := globalNonreducedIdealSheaf_unconditional_closed S v W
  lift := globalLocalizationLiftGluing_unconditional S v

theorem unconditionalGlobalNonreducedIdealSheafData_idealSheaf
    (W : WeierstrassCurve (kernelBase S v)) :
    (unconditionalGlobalNonreducedIdealSheafData S v W).idealSheaf =
      globalNonreducedIdealSheaf_unconditional S v W :=
  rfl

theorem unconditionalGlobalNonreducedIdealSheafData_chart
    (W : WeierstrassCurve (kernelBase S v)) (i : Fin 3) :
    (unconditionalGlobalNonreducedIdealSheafData S v W).idealSheaf.ideal
        (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v i :=
  (unconditionalGlobalNonreducedIdealSheafData S v W).chartRestriction i

theorem unconditionalGlobalNonreducedIdealSheafData_closed
    (W : WeierstrassCurve (kernelBase S v)) :
    IsClosedImmersion
      (unconditionalGlobalNonreducedIdealSheafData S v W).idealSheaf.subschemeι :=
  (unconditionalGlobalNonreducedIdealSheafData S v W).closed

theorem unconditionalGlobalNonreducedIdealSheafData_lift
    (W : WeierstrassCurve (kernelBase S v)) :
    GlobalLocalizationLiftGluing S v :=
  (unconditionalGlobalNonreducedIdealSheafData S v W).lift

theorem unconditionalGlobalNonreducedIdealSheafData_actual
    (W : WeierstrassCurve (kernelBase S v)) :
    (∀ i : Fin 3,
      (unconditionalGlobalNonreducedIdealSheafData S v W).idealSheaf.ideal
        (projectiveStandardChartAffine S v i) =
        projectiveNonreducedChartIdeal S v i) ∧
      IsClosedImmersion
        (unconditionalGlobalNonreducedIdealSheafData S v W).idealSheaf.subschemeι :=
  ⟨fun i => unconditionalGlobalNonreducedIdealSheafData_chart S v W i,
    unconditionalGlobalNonreducedIdealSheafData_closed S v W⟩

theorem unconditionalGlobalNonreducedIdealSheafData_ideal_family
    (W : WeierstrassCurve (kernelBase S v))
    (U : (glueX S v).affineOpens) :
    (unconditionalGlobalNonreducedIdealSheafData S v W).idealSheaf.ideal U =
      globalIdealFamily S v W U :=
  rfl

theorem overlapKernelAnnihilation_unconditional_consumer :
    OverlapKernelAnnihilationStatement S v ∧
      GlobalLocalizationLiftGluing S v :=
  ⟨overlapKernelAnnihilationStatement_holds S v,
    globalLocalizationLiftGluing_unconditional S v⟩

end LeanFormal.IUT.OverlapKernelAnnihilationProof
