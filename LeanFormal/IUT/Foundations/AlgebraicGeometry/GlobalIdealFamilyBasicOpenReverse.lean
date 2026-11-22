import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalIdealFamilyBasicOpenProof
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

/-!
# Reverse basic-open inclusion for the global ideal family

The reverse inclusion is localized: a section on a basic open D(f) that lies in
the global ideal family can be multiplied by a power of f and then lifted to a
family section on the affine open U.  This exact localization-lift statement is
the remaining sheaf-theoretic input; it is isolated.  From it the reverse
inclusion, the GlobalIdealFamilyBasicOpenResidual and the conditional global
non-reduced ideal sheaf follow by actual arguments.  No fake sheaf.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.GlobalIdealFamilyBasicOpenReverse

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
open MvPolynomial AlgebraicGeometry
open scoped Polynomial BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

abbrev reverseBase : Type u := basicOpenBase S v
abbrev reverseX : Scheme.{u} := basicOpenProj S v

/-- The actual localization-lift input: every family section on D(f) becomes,
after multiplying by a power of f, the restriction of a family section on U. -/
def GlobalIdealFamilyLocalizationLift
    (W : WeierstrassCurve (reverseBase S v)) : Prop :=
  ∀ (U : (reverseX S v).affineOpens)
    (f : Γ(reverseX S v, U))
    (y : Γ(reverseX S v, (reverseX S v).affineBasicOpen f)),
    y ∈ globalIdealFamily S v W ((reverseX S v).affineBasicOpen f) →
      ∃ (N : ℕ) (x : Γ(reverseX S v, U)),
        x ∈ globalIdealFamily S v W U ∧
          ((reverseX S v).presheaf.map
            (homOfLE ((reverseX S v).basicOpen_le f)).op).hom x =
            (f ^ N) * y

/-- From the exact localization-lift input, the reverse inclusion follows by
using that f is a unit on D(f). -/
theorem globalIdealFamilyBasicOpenReverse_of_lift
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) :
    GlobalIdealFamilyBasicOpenReverse S v W :=
  by
  intro U f
  rw [Ideal.map_le_iff_le_comap]
  intro y hy
  rw [Ideal.mem_comap]
  obtain ⟨N, x, hx, hfac⟩ := hLift U f y hy
  -- f is a unit in the localized basic-open section ring, so the power f^N
  -- can be cancelled through the ideal-map image.
  have hunit : IsUnit (f ^ N : Γ(reverseX S v,
      (reverseX S v).affineBasicOpen f)) :=
    (IsLocalization.Away.algebraMap_isUnit f N)
  rcases hunit with ⟨u, hu⟩
  have hxmem : ((reverseX S v).presheaf.map
        (homOfLE ((reverseX S v).basicOpen_le f)).op).hom x ∈
      (globalIdealFamily S v W U).map
        ((reverseX S v).presheaf.map
          (homOfLE ((reverseX S v).basicOpen_le f)).op).hom :=
    Ideal.mem_map_of_mem _ hx
  have hy_eq : y = u * ((reverseX S v).presheaf.map
        (homOfLE ((reverseX S v).basicOpen_le f)).op).hom x := by
    rw [hfac, hu, mul_comm]
  rw [hy_eq]
  exact Ideal.mul_mem_left _ u hxmem

/-- The reverse lemma from the localization-lift input. -/
noncomputable def globalIdealFamilyBasicOpenReverseLemma_of_lift
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) :
    GlobalIdealFamilyBasicOpenReverseLemma S v W where
  reverse := globalIdealFamilyBasicOpenReverse_of_lift S v W hLift

/-- The basic-open residual from the localization-lift input. -/
noncomputable def globalIdealFamilyBasicOpenResidual_of_lift
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) :
    GlobalIdealFamilyBasicOpenResidual S v W :=
  globalIdealFamilyBasicOpenResidualOfReverse S v W
    (globalIdealFamilyBasicOpenReverseLemma_of_lift S v W hLift)

/-- The exact gluing input from the localization-lift input. -/
noncomputable def projectiveIdealSheafGluingInput_of_lift
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) :
    ProjectiveIdealSheafGluingInput S v W :=
  projectiveIdealSheafGluingInputOfFamily S v W
    (globalIdealFamilyBasicOpenResidual_of_lift S v W hLift)

theorem projectiveIdealSheafGluingInput_of_lift_chart
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) (i : Fin 3) :
    (projectiveIdealSheafGluingInput_of_lift S v W hLift).ideal
        (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v W i :=
  globalIdealFamily_chart S v W i

theorem projectiveIdealSheafGluingInput_of_lift_map
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W)
    (U : (reverseX S v).affineOpens)
    (f : Γ(reverseX S v, U)) :
    ((projectiveIdealSheafGluingInput_of_lift S v W hLift).ideal U).map
        ((reverseX S v).presheaf.map
          (homOfLE ((reverseX S v).basicOpen_le f)).op).hom =
      (projectiveIdealSheafGluingInput_of_lift S v W hLift).ideal
        ((reverseX S v).affineBasicOpen f) :=
  (projectiveIdealSheafGluingInput_of_lift S v W hLift).map_ideal_basicOpen U f

/-- The conditional actual global non-reduced ideal sheaf from the exact
localization-lift input. -/
noncomputable def globalNonreducedIdealSheaf_of_lift
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) :
    (reverseX S v).IdealSheafData :=
  gluedIdealSheaf S v W (projectiveIdealSheafGluingInput_of_lift S v W hLift)

theorem globalNonreducedIdealSheaf_of_lift_ideal
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W)
    (U : (reverseX S v).affineOpens) :
    (globalNonreducedIdealSheaf_of_lift S v W hLift).ideal U =
      globalIdealFamily S v W U :=
  rfl

theorem globalNonreducedIdealSheaf_of_lift_chart
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) (i : Fin 3) :
    (globalNonreducedIdealSheaf_of_lift S v W hLift).ideal
        (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v W i :=
  globalIdealFamily_chart S v W i

theorem globalNonreducedIdealSheaf_of_lift_support
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) :
    (globalNonreducedIdealSheaf_of_lift S v W hLift).support =
      ⟨⋂ U, (reverseX S v).zeroLocus (U := U.1)
        (globalIdealFamily S v W U),
        (globalNonreducedIdealSheaf_of_lift S v W hLift).isClosed_supportSet⟩ :=
  rfl

/-- Conditional closure of the global non-reduced ideal-sheaf construction:
the exact localization-lift input closes the basic-open residual and yields the
actual global ideal sheaf. -/
theorem globalNonreducedIdealSheaf_conditional_closed
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) :
    GlobalIdealFamilyBasicOpenResidualStatement S v W ∧
      (globalNonreducedIdealSheaf_of_lift S v W hLift).ideal =
        globalIdealFamily S v W :=
  ⟨globalIdealFamilyBasicOpenReverse_of_lift S v W hLift,
    funext fun U => rfl⟩

theorem globalIdealFamilyBasicOpenResidualStatement_of_lift
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) :
    GlobalIdealFamilyBasicOpenResidualStatement S v W :=
  globalIdealFamilyBasicOpenReverse_of_lift S v W hLift

theorem globalIdealFamilyBasicOpenResidualStatement_consumer
    (W : WeierstrassCurve (reverseBase S v)) :
    GlobalIdealFamilyBasicOpenResidualStatement S v W ↔
      GlobalIdealFamilyBasicOpenReverse S v W :=
  Iff.rfl

theorem projectiveIdealSheafGluingInput_of_lift_ideal
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W)
    (U : (reverseX S v).affineOpens) :
    (projectiveIdealSheafGluingInput_of_lift S v W hLift).ideal U =
      globalIdealFamily S v W U :=
  rfl

abbrev globalNonreducedIdealSheafOfLiftClosedSubscheme
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) : Scheme.{u} :=
  (globalNonreducedIdealSheaf_of_lift S v W hLift).subscheme

theorem globalNonreducedIdealSheafOfLift_range
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) :
    Set.range (globalNonreducedIdealSheaf_of_lift S v W hLift).subschemeι =
      ((globalNonreducedIdealSheaf_of_lift S v W hLift).support :
        Set (reverseX S v)) :=
  (globalNonreducedIdealSheaf_of_lift S v W hLift).range_subschemeι

structure GlobalNonreducedIdealSheafFinalData
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) where
  idealSheaf : (reverseX S v).IdealSheafData
  idealSheaf_eq : idealSheaf = globalNonreducedIdealSheaf_of_lift S v W hLift
  chartRestriction : ∀ i : Fin 3,
    idealSheaf.ideal (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v W i
  basicOpenResidual : GlobalIdealFamilyBasicOpenResidualStatement S v W
  support_eq : idealSheaf.support =
    ⟨⋂ U, (reverseX S v).zeroLocus (U := U.1)
      (globalIdealFamily S v W U), idealSheaf.isClosed_supportSet⟩

noncomputable def globalNonreducedIdealSheafFinalData
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) :
    GlobalNonreducedIdealSheafFinalData S v W hLift where
  idealSheaf := globalNonreducedIdealSheaf_of_lift S v W hLift
  idealSheaf_eq := rfl
  chartRestriction := fun i =>
    globalNonreducedIdealSheaf_of_lift_chart S v W hLift i
  basicOpenResidual :=
    globalIdealFamilyBasicOpenResidualStatement_of_lift S v W hLift
  support_eq := globalNonreducedIdealSheaf_of_lift_support S v W hLift

theorem globalNonreducedIdealSheafFinalData_idealSheaf
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) :
    (globalNonreducedIdealSheafFinalData S v W hLift).idealSheaf =
      globalNonreducedIdealSheaf_of_lift S v W hLift :=
  rfl

theorem globalNonreducedIdealSheafFinalData_chart
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) (i : Fin 3) :
    (globalNonreducedIdealSheafFinalData S v W hLift).idealSheaf.ideal
        (projectiveStandardChartAffine S v i) =
      projectiveNonreducedChartIdeal S v W i :=
  (globalNonreducedIdealSheafFinalData S v W hLift).chartRestriction i

theorem globalNonreducedIdealSheafFinalData_residual
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) :
    (globalNonreducedIdealSheafFinalData S v W hLift).basicOpenResidual :=
  (globalNonreducedIdealSheafFinalData S v W hLift).basicOpenResidual

theorem globalNonreducedIdealSheafFinalData_support
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) :
    (globalNonreducedIdealSheafFinalData S v W hLift).idealSheaf.support =
      ⟨⋂ U, (reverseX S v).zeroLocus (U := U.1)
        (globalIdealFamily S v W U),
        (globalNonreducedIdealSheafFinalData S v W hLift).idealSheaf.isClosed_supportSet⟩ :=
  (globalNonreducedIdealSheafFinalData S v W hLift).support_eq

theorem globalNonreducedIdealSheaf_of_lift_chart_all
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) :
    ∀ i : Fin 3,
      (globalNonreducedIdealSheaf_of_lift S v W hLift).ideal
        (projectiveStandardChartAffine S v i) =
        projectiveNonreducedChartIdeal S v W i :=
  fun i => globalNonreducedIdealSheaf_of_lift_chart S v W hLift i

theorem globalNonreducedIdealSheaf_of_lift_ideal_family
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) :
    (globalNonreducedIdealSheaf_of_lift S v W hLift).ideal =
      globalIdealFamily S v W :=
  funext fun U => rfl

theorem globalNonreducedIdealSheafFinalData_chart_all
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) :
    ∀ i : Fin 3,
      (globalNonreducedIdealSheafFinalData S v W hLift).idealSheaf.ideal
        (projectiveStandardChartAffine S v i) =
        projectiveNonreducedChartIdeal S v W i :=
  fun i => globalNonreducedIdealSheafFinalData_chart S v W hLift i

theorem globalNonreducedIdealSheafFinalData_actual
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) :
    (globalNonreducedIdealSheafFinalData S v W hLift).idealSheaf.support =
        ⟨⋂ U, (reverseX S v).zeroLocus (U := U.1)
          (globalIdealFamily S v W U),
          (globalNonreducedIdealSheafFinalData S v W hLift).idealSheaf.isClosed_supportSet⟩ ∧
      (∀ i : Fin 3,
        (globalNonreducedIdealSheafFinalData S v W hLift).idealSheaf.ideal
          (projectiveStandardChartAffine S v i) =
          projectiveNonreducedChartIdeal S v W i) :=
  ⟨globalNonreducedIdealSheafFinalData_support S v W hLift,
    globalNonreducedIdealSheafFinalData_chart_all S v W hLift⟩

theorem globalIdealFamilyReverse_conditional_closed
    (W : WeierstrassCurve (reverseBase S v))
    (hLift : GlobalIdealFamilyLocalizationLift S v W) :
    GlobalIdealFamilyBasicOpenResidualStatement S v W ∧
      Nonempty (GlobalNonreducedIdealSheafFinalData S v W hLift) :=
  ⟨globalIdealFamilyBasicOpenResidualStatement_of_lift S v W hLift,
    ⟨globalNonreducedIdealSheafFinalData S v W hLift⟩⟩

end LeanFormal.IUT.GlobalIdealFamilyBasicOpenReverse
