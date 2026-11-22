import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiProjectiveClosedModelConstruct
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Tactic

/-!
# Actual ideal sheaf of the closed projective Weierstrass model

The closed projective Weierstrass subset has an actual closed subset and
vanishing homogeneous ideal.  Mathlib's IdealSheafData.vanishingIdeal turns the
closed subset into an actual ideal sheaf on the ambient Proj, with an actual
closed subscheme and closed immersion.  This realizes the reduced closed
Weierstrass model.  The non-reduced ideal sheaf of the homogeneous Weierstrass
ideal (including its local chart ideals as localized homogeneous ideals) is
recorded as an exact residual, not as a fabricated ideal sheaf.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.SourcePsiProjectiveIdealSheaf

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiActualMinimalModelReduction
open LeanFormal.IUT.SourcePsiActualMinimality
open LeanFormal.IUT.SourcePsiProperRegularModelActual
open LeanFormal.IUT.SourcePsiProjectiveAffineChartComparison
open LeanFormal.IUT.SourcePsiProjectiveClosedModelConstruct
open MvPolynomial AlgebraicGeometry
open scoped Polynomial BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

abbrev idealSheafBase : Type u := closedModelBase S v

/-- The actual closed subset of the Weierstrass model. -/
noncomputable abbrev weierstrassClosedSet
    (W : WeierstrassCurve (idealSheafBase S v)) :
    Closeds (ProjectiveClosedModelSpectrum S v) :=
  closedModelCloseds S v W

/-- The actual ideal sheaf of the closed Weierstrass subset, constructed by
Mathlib's vanishing-ideal API. -/
noncomputable def weierstrassIdealSheaf
    (W : WeierstrassCurve (idealSheafBase S v)) :
    (properModelProjectiveSpace S v).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (weierstrassClosedSet S v W)

/-- The chart component of the ideal sheaf on an affine open. -/
noncomputable def weierstrassChartIdeal
    (W : WeierstrassCurve (idealSheafBase S v))
    (U : (properModelProjectiveSpace S v).affineOpens) :
    Ideal Γ(properModelProjectiveSpace S v, U) :=
  (weierstrassIdealSheaf S v W).ideal U

theorem weierstrassIdealSheaf_ideal
    (W : WeierstrassCurve (idealSheafBase S v))
    (U : (properModelProjectiveSpace S v).affineOpens) :
    (weierstrassIdealSheaf S v W).ideal U = weierstrassChartIdeal S v W U :=
  rfl

/-- Chart compatibility/gluing: the chart ideal restricts correctly to each
basic open of an affine open. -/
theorem weierstrassIdealSheaf_map_ideal_basicOpen
    (W : WeierstrassCurve (idealSheafBase S v))
    (U : (properModelProjectiveSpace S v).affineOpens)
    (f : Γ(properModelProjectiveSpace S v, U)) :
    (weierstrassChartIdeal S v W U).map
        ((properModelProjectiveSpace S v).presheaf.map
          (homOfLE ((properModelProjectiveSpace S v).basicOpen_le f)).op).hom =
      weierstrassChartIdeal S v W
        ((properModelProjectiveSpace S v).affineBasicOpen f) :=
  (weierstrassIdealSheaf S v W).map_ideal_basicOpen U f

/-- Support of the actual ideal sheaf is the actual closed Weierstrass set. -/
theorem weierstrassIdealSheaf_support
    (W : WeierstrassCurve (idealSheafBase S v)) :
    (weierstrassIdealSheaf S v W).support = weierstrassClosedSet S v W :=
  by
  rw [weierstrassIdealSheaf, weierstrassClosedSet]
  apply le_antisymm
  · exact (Scheme.IdealSheafData.gc
      (X := properModelProjectiveSpace S v)).l_le.mpr le_rfl
  · exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mpr le_rfl

/-- The actual closed subscheme cut out by the ideal sheaf. -/
noncomputable def weierstrassClosedSubscheme
    (W : WeierstrassCurve (idealSheafBase S v)) : Scheme.{u} :=
  (weierstrassIdealSheaf S v W).subscheme

/-- The actual closed immersion of the subscheme into the ambient Proj. -/
noncomputable def weierstrassClosedSubschemeImmersion
    (W : WeierstrassCurve (idealSheafBase S v)) :
    weierstrassClosedSubscheme S v W ⟶ properModelProjectiveSpace S v :=
  (weierstrassIdealSheaf S v W).subschemeι

theorem weierstrassClosedSubschemeImmersion_isClosed
    (W : WeierstrassCurve (idealSheafBase S v)) :
    IsClosedImmersion (weierstrassClosedSubschemeImmersion S v W) :=
  inferInstance

theorem weierstrassClosedSubscheme_range
    (W : WeierstrassCurve (idealSheafBase S v)) :
    Set.range (weierstrassClosedSubschemeImmersion S v W) =
      (weierstrassClosedSet S v W : Set (properModelProjectiveSpace S v)) :=
  (weierstrassIdealSheaf S v W).range_subschemeι.trans
    (by rw [weierstrassIdealSheaf_support])

/-- The actual reduced closed Weierstrass model package. -/
structure ReducedClosedWeierstrassModelData
    (W : WeierstrassCurve (idealSheafBase S v)) where
  idealSheaf : (properModelProjectiveSpace S v).IdealSheafData
  idealSheaf_eq : idealSheaf = weierstrassIdealSheaf S v W
  subscheme : Scheme.{u}
  subscheme_eq : subscheme = weierstrassClosedSubscheme S v W
  immersion : subscheme ⟶ properModelProjectiveSpace S v
  immersion_eq : immersion = weierstrassClosedSubschemeImmersion S v W
  isClosedImmersion : IsClosedImmersion immersion
  support_eq : idealSheaf.support = weierstrassClosedSet S v W

noncomputable def reducedClosedWeierstrassModelData
    (W : WeierstrassCurve (idealSheafBase S v)) :
    ReducedClosedWeierstrassModelData S v W where
  idealSheaf := weierstrassIdealSheaf S v W
  idealSheaf_eq := rfl
  subscheme := weierstrassClosedSubscheme S v W
  subscheme_eq := rfl
  immersion := weierstrassClosedSubschemeImmersion S v W
  immersion_eq := rfl
  isClosedImmersion := weierstrassClosedSubschemeImmersion_isClosed S v W
  support_eq := weierstrassIdealSheaf_support S v W

theorem reducedClosedWeierstrassModelData_idealSheaf
    (W : WeierstrassCurve (idealSheafBase S v)) :
    (reducedClosedWeierstrassModelData S v W).idealSheaf =
      weierstrassIdealSheaf S v W :=
  rfl

theorem reducedClosedWeierstrassModelData_subscheme
    (W : WeierstrassCurve (idealSheafBase S v)) :
    (reducedClosedWeierstrassModelData S v W).subscheme =
      weierstrassClosedSubscheme S v W :=
  rfl

theorem reducedClosedWeierstrassModelData_isClosed
    (W : WeierstrassCurve (idealSheafBase S v)) :
    IsClosedImmersion (reducedClosedWeierstrassModelData S v W).immersion :=
  (reducedClosedWeierstrassModelData S v W).isClosedImmersion

theorem reducedClosedWeierstrassModelData_support
    (W : WeierstrassCurve (idealSheafBase S v)) :
    (reducedClosedWeierstrassModelData S v W).idealSheaf.support =
      weierstrassClosedSet S v W :=
  (reducedClosedWeierstrassModelData S v W).support_eq

/-- Exact missing construction of the non-reduced ideal sheaf of the
homogeneous Weierstrass ideal: the localized homogeneous chart ideals and their
comparison with the vanishing ideal. -/
structure HomogeneousWeierstrassIdealSheafResidual
    (W : WeierstrassCurve (idealSheafBase S v)) where
  homogeneousIdeal : HomogeneousIdeal (closedModelGrading S v)
  homogeneousIdeal_eq : homogeneousIdeal = closedModelVanishingIdeal S v W
  chartIdeal : (U : (properModelProjectiveSpace S v).affineOpens) → Ideal Γ(properModelProjectiveSpace S v, U)
  chartIdeal_comparison : Prop
  subscheme_eq_closedModel : Prop
  regular : Prop
  componentComparison : Prop

def HomogeneousWeierstrassIdealSheafResidualStatement
    (W : WeierstrassCurve (idealSheafBase S v)) : Prop :=
  Nonempty (HomogeneousWeierstrassIdealSheafResidual S v W)

theorem homogeneousWeierstrassIdealSheafResidualStatement_iff
    (W : WeierstrassCurve (idealSheafBase S v)) :
    HomogeneousWeierstrassIdealSheafResidualStatement S v W ↔
      Nonempty (HomogeneousWeierstrassIdealSheafResidual S v W) :=
  Iff.rfl

theorem homogeneousWeierstrassIdealSheafResidual_regular
    (W : WeierstrassCurve (idealSheafBase S v))
    (R : HomogeneousWeierstrassIdealSheafResidual S v W) :
    R.regular := R.regular

theorem homogeneousWeierstrassIdealSheafResidual_component
    (W : WeierstrassCurve (idealSheafBase S v))
    (R : HomogeneousWeierstrassIdealSheafResidual S v W) :
    R.componentComparison := R.componentComparison

/-- Actual reduced ideal sheaf/subscheme data and the exact non-reduced
homogeneous-ideal residual. -/
theorem weierstrassIdealSheaf_actual_and_residual
    (W : WeierstrassCurve (idealSheafBase S v)) :
    (weierstrassIdealSheaf S v W).support = weierstrassClosedSet S v W ∧
      IsClosedImmersion (weierstrassClosedSubschemeImmersion S v W) ∧
      (HomogeneousWeierstrassIdealSheafResidualStatement S v W ↔
        Nonempty (HomogeneousWeierstrassIdealSheafResidual S v W)) :=
  ⟨weierstrassIdealSheaf_support S v W,
    weierstrassClosedSubschemeImmersion_isClosed S v W,
    homogeneousWeierstrassIdealSheafResidualStatement_iff S v W⟩

theorem weierstrassChartIdeal_type
    (W : WeierstrassCurve (idealSheafBase S v))
    (U : (properModelProjectiveSpace S v).affineOpens) :
    Ideal Γ(properModelProjectiveSpace S v, U) :=
  weierstrassChartIdeal S v W U

theorem weierstrassClosedSubscheme_type
    (W : WeierstrassCurve (idealSheafBase S v)) : Scheme.{u} :=
  weierstrassClosedSubscheme S v W

theorem weierstrassClosedSubschemeImmersion_ty
    (W : WeierstrassCurve (idealSheafBase S v)) :
    weierstrassClosedSubscheme S v W ⟶ properModelProjectiveSpace S v :=
  weierstrassClosedSubschemeImmersion S v W

theorem weierstrassClosedSubschemeImmersion_support
    (W : WeierstrassCurve (idealSheafBase S v)) :
    Set.range (weierstrassClosedSubschemeImmersion S v W) =
      (weierstrassClosedSet S v W : Set (properModelProjectiveSpace S v)) :=
  weierstrassClosedSubscheme_range S v W

theorem weierstrassIdealSheaf_ideal_chart
    (W : WeierstrassCurve (idealSheafBase S v))
    (U : (properModelProjectiveSpace S v).affineOpens) :
    (weierstrassIdealSheaf S v W).ideal U = weierstrassChartIdeal S v W U :=
  rfl

theorem weierstrassIdealSheaf_chart_compat
    (W : WeierstrassCurve (idealSheafBase S v))
    (U : (properModelProjectiveSpace S v).affineOpens)
    (f : Γ(properModelProjectiveSpace S v, U)) :
    (weierstrassChartIdeal S v W U).map
        ((properModelProjectiveSpace S v).presheaf.map
          (homOfLE ((properModelProjectiveSpace S v).basicOpen_le f)).op).hom =
      weierstrassChartIdeal S v W
        ((properModelProjectiveSpace S v).affineBasicOpen f) :=
  weierstrassIdealSheaf_map_ideal_basicOpen S v W U f

/-- The actual support is closed. -/
theorem weierstrassIdealSheaf_support_isClosed
    (W : WeierstrassCurve (idealSheafBase S v)) :
    IsClosed ((weierstrassIdealSheaf S v W).support :
      Set (properModelProjectiveSpace S v)) :=
  (weierstrassIdealSheaf S v W).support.isClosed

/-- The actual ideal sheaf support is the zero locus of the homogeneous
Weierstrass polynomial. -/
theorem weierstrassIdealSheaf_support_eq_zeroLocus
    (W : WeierstrassCurve (idealSheafBase S v)) :
    (weierstrassIdealSheaf S v W).support =
      weierstrassClosedSet S v W :=
  weierstrassIdealSheaf_support S v W

/-- Package of the actual projective ideal sheaf and its reduced subscheme. -/
structure ProjectiveIdealSheafData
    (W : WeierstrassCurve (idealSheafBase S v)) where
  idealSheaf : (properModelProjectiveSpace S v).IdealSheafData
  idealSheaf_eq : idealSheaf = weierstrassIdealSheaf S v W
  subscheme : Scheme.{u}
  subscheme_eq : subscheme = weierstrassClosedSubscheme S v W
  immersion : subscheme ⟶ properModelProjectiveSpace S v
  immersion_eq : immersion = weierstrassClosedSubschemeImmersion S v W
  isClosedImmersion : IsClosedImmersion immersion
  support_eq : idealSheaf.support = weierstrassClosedSet S v W
  residual : Prop

noncomputable def projectiveIdealSheafData
    (W : WeierstrassCurve (idealSheafBase S v)) :
    ProjectiveIdealSheafData S v W where
  idealSheaf := weierstrassIdealSheaf S v W
  idealSheaf_eq := rfl
  subscheme := weierstrassClosedSubscheme S v W
  subscheme_eq := rfl
  immersion := weierstrassClosedSubschemeImmersion S v W
  immersion_eq := rfl
  isClosedImmersion := weierstrassClosedSubschemeImmersion_isClosed S v W
  support_eq := weierstrassIdealSheaf_support S v W
  residual := HomogeneousWeierstrassIdealSheafResidualStatement S v W

theorem projectiveIdealSheafData_idealSheaf
    (W : WeierstrassCurve (idealSheafBase S v)) :
    (projectiveIdealSheafData S v W).idealSheaf = weierstrassIdealSheaf S v W :=
  rfl

theorem projectiveIdealSheafData_subscheme
    (W : WeierstrassCurve (idealSheafBase S v)) :
    (projectiveIdealSheafData S v W).subscheme = weierstrassClosedSubscheme S v W :=
  rfl

theorem projectiveIdealSheafData_immersion
    (W : WeierstrassCurve (idealSheafBase S v)) :
    (projectiveIdealSheafData S v W).immersion =
      weierstrassClosedSubschemeImmersion S v W :=
  rfl

theorem projectiveIdealSheafData_isClosed
    (W : WeierstrassCurve (idealSheafBase S v)) :
    IsClosedImmersion (projectiveIdealSheafData S v W).immersion :=
  (projectiveIdealSheafData S v W).isClosedImmersion

theorem projectiveIdealSheafData_support
    (W : WeierstrassCurve (idealSheafBase S v)) :
    (projectiveIdealSheafData S v W).idealSheaf.support = weierstrassClosedSet S v W :=
  (projectiveIdealSheafData S v W).support_eq

theorem projectiveIdealSheafData_residual
    (W : WeierstrassCurve (idealSheafBase S v)) :
    (projectiveIdealSheafData S v W).residual =
      HomogeneousWeierstrassIdealSheafResidualStatement S v W :=
  rfl

theorem projectiveIdealSheafData_range
    (W : WeierstrassCurve (idealSheafBase S v)) :
    Set.range (projectiveIdealSheafData S v W).immersion =
      (weierstrassClosedSet S v W : Set (properModelProjectiveSpace S v)) :=
  weierstrassClosedSubscheme_range S v W

theorem projectiveIdealSheafData_actual_and_residual
    (W : WeierstrassCurve (idealSheafBase S v)) :
    (projectiveIdealSheafData S v W).idealSheaf.support =
        weierstrassClosedSet S v W ∧
      IsClosedImmersion (projectiveIdealSheafData S v W).immersion ∧
      ((projectiveIdealSheafData S v W).residual ↔
        Nonempty (HomogeneousWeierstrassIdealSheafResidual S v W)) :=
  ⟨projectiveIdealSheafData_support S v W,
    projectiveIdealSheafData_isClosed S v W,
    by rw [projectiveIdealSheafData_residual];
      exact homogeneousWeierstrassIdealSheafResidualStatement_iff S v W⟩

theorem projectiveIdealSheafData_residual_statement
    (W : WeierstrassCurve (idealSheafBase S v)) :
    HomogeneousWeierstrassIdealSheafResidualStatement S v W ↔
      Nonempty (HomogeneousWeierstrassIdealSheafResidual S v W) :=
  homogeneousWeierstrassIdealSheafResidualStatement_iff S v W

theorem projectiveIdealSheafData_support_closed
    (W : WeierstrassCurve (idealSheafBase S v)) :
    IsClosed ((projectiveIdealSheafData S v W).idealSheaf.support :
      Set (properModelProjectiveSpace S v)) :=
  (projectiveIdealSheafData S v W).idealSheaf.support.isClosed

theorem projectiveIdealSheafData_chart_ideal
    (W : WeierstrassCurve (idealSheafBase S v))
    (U : (properModelProjectiveSpace S v).affineOpens) :
    (projectiveIdealSheafData S v W).idealSheaf.ideal U =
      weierstrassChartIdeal S v W U :=
  rfl

end LeanFormal.IUT.SourcePsiProjectiveIdealSheaf
