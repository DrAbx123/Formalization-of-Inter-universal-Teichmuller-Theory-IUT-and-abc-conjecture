import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiProperRegularModelActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiProjectiveAffineChartComparison
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Tactic

/-!
# Actual closed projective model: closed subset and exact scheme residual

Mathlib's projective spectrum supplies the actual closed subset cut out by the
homogeneous Weierstrass polynomial, together with its vanishing homogeneous
ideal.  The ambient Proj is an actual proper scheme.  The passage from this
closed subset to an actual closed subscheme is not available in the frozen
API, so it is recorded as an exact residual structure, not as a fabricated
closed subscheme.  Regularity and component comparison remain in that residual.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.SourcePsiProjectiveClosedModelConstruct

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiActualMinimalModelReduction
open LeanFormal.IUT.SourcePsiActualMinimality
open LeanFormal.IUT.SourcePsiProperRegularModelActual
open LeanFormal.IUT.SourcePsiProjectiveAffineChartComparison
open MvPolynomial AlgebraicGeometry
open scoped Polynomial BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

abbrev closedModelBase : Type u := properModelBase S v

abbrev closedModelGrading : ℕ → Submodule (closedModelBase S v)
    (MvPolynomial (Fin 3) (closedModelBase S v)) :=
  MvPolynomial.homogeneousSubmodule (Fin 3) (closedModelBase S v)

abbrev ProjectiveClosedModelSpectrum : Type u :=
  ProjectiveSpectrum (closedModelGrading S v)

noncomputable def closedModelPolynomial
    (W : WeierstrassCurve (closedModelBase S v)) :
    MvPolynomial (Fin 3) (closedModelBase S v) :=
  properModelWeierstrassPolynomial S v W

noncomputable def closedModelSubset
    (W : WeierstrassCurve (closedModelBase S v)) :
    Set (ProjectiveClosedModelSpectrum S v) :=
  ProjectiveSpectrum.zeroLocus (closedModelGrading S v) {closedModelPolynomial S v W}

theorem closedModelSubset_isClosed
    (W : WeierstrassCurve (closedModelBase S v)) :
    IsClosed (closedModelSubset S v W) :=
  ProjectiveSpectrum.isClosed_zeroLocus _ _

theorem mem_closedModelSubset_iff
    (W : WeierstrassCurve (closedModelBase S v))
    (P : ProjectiveClosedModelSpectrum S v) :
    P ∈ closedModelSubset S v W ↔
      closedModelPolynomial S v W ∈ P.asHomogeneousIdeal :=
  Iff.rfl

noncomputable def closedModelCloseds
    (W : WeierstrassCurve (closedModelBase S v)) :
    Closeds (ProjectiveClosedModelSpectrum S v) :=
  ⟨closedModelSubset S v W, closedModelSubset_isClosed S v W⟩

theorem closedModelCloseds_coe
    (W : WeierstrassCurve (closedModelBase S v)) :
    (closedModelCloseds S v W : Set (ProjectiveClosedModelSpectrum S v)) =
      closedModelSubset S v W :=
  rfl

noncomputable def closedModelVanishingIdeal
    (W : WeierstrassCurve (closedModelBase S v)) :
    HomogeneousIdeal (closedModelGrading S v) :=
  ProjectiveSpectrum.vanishingIdeal (closedModelGrading S v) (closedModelSubset S v W)

theorem closedModelSubset_eq_zeroLocus_vanishingIdeal
    (W : WeierstrassCurve (closedModelBase S v)) :
    closedModelSubset S v W =
      ProjectiveSpectrum.zeroLocus (closedModelGrading S v)
        (closedModelVanishingIdeal S v W : Set
          (MvPolynomial (Fin 3) (closedModelBase S v))) :=
  by
  rw [closedModelSubset]
  exact (ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure _ _).trans
    (by rw [ProjectiveSpectrum.closure_eq_self_of_isClosed
      (closedModelSubset_isClosed S v W)])

structure ProjectiveClosedModelSubsetData
    (W : WeierstrassCurve (closedModelBase S v)) where
  closedSet : Closeds (ProjectiveClosedModelSpectrum S v)
  closedSet_eq : closedSet = closedModelCloseds S v W
  vanishingIdeal : HomogeneousIdeal (closedModelGrading S v)
  vanishingIdeal_eq : vanishingIdeal = closedModelVanishingIdeal S v W
  isClosed : IsClosed (closedModelSubset S v W)

noncomputable def projectiveClosedModelSubsetData
    (W : WeierstrassCurve (closedModelBase S v)) :
    ProjectiveClosedModelSubsetData S v W where
  closedSet := closedModelCloseds S v W
  closedSet_eq := rfl
  vanishingIdeal := closedModelVanishingIdeal S v W
  vanishingIdeal_eq := rfl
  isClosed := closedModelSubset_isClosed S v W

theorem projectiveClosedModelSubsetData_closedSet
    (W : WeierstrassCurve (closedModelBase S v)) :
    (projectiveClosedModelSubsetData S v W).closedSet =
      closedModelCloseds S v W :=
  rfl

theorem projectiveClosedModelSubsetData_vanishingIdeal
    (W : WeierstrassCurve (closedModelBase S v)) :
    (projectiveClosedModelSubsetData S v W).vanishingIdeal =
      closedModelVanishingIdeal S v W :=
  rfl

structure MissingClosedSubschemeAPI
    (W : WeierstrassCurve (closedModelBase S v)) where
  closedSubscheme : Scheme.{u}
  immersion : closedSubscheme ⟶ properModelProjectiveSpace S v
  isClosedImmersion : IsClosedImmersion immersion
  support_eq_closedSet : Prop
  homogeneousIdeal_comparison : Prop
  regular : Prop
  componentComparison : Prop

def MissingClosedSubschemeAPIStatement
    (W : WeierstrassCurve (closedModelBase S v)) : Prop :=
  Nonempty (MissingClosedSubschemeAPI S v W)

theorem missingClosedSubschemeAPIStatement_iff
    (W : WeierstrassCurve (closedModelBase S v)) :
    MissingClosedSubschemeAPIStatement S v W ↔
      Nonempty (MissingClosedSubschemeAPI S v W) :=
  Iff.rfl

theorem missingClosedSubschemeAPI_immersion
    (W : WeierstrassCurve (closedModelBase S v))
    (R : MissingClosedSubschemeAPI S v W) :
    IsClosedImmersion R.immersion :=
  R.isClosedImmersion

theorem missingClosedSubschemeAPI_regular
    (W : WeierstrassCurve (closedModelBase S v))
    (R : MissingClosedSubschemeAPI S v W) :
    R.regular := R.regular

theorem missingClosedSubschemeAPI_component
    (W : WeierstrassCurve (closedModelBase S v))
    (R : MissingClosedSubschemeAPI S v W) :
    R.componentComparison := R.componentComparison

theorem ambientProjectiveSpace_isProper :
    IsProper (properModelProjectiveStructureMap S v) :=
  properModelProjectiveSpace_isProper S v

theorem closedModelSubset_contained_in_ambient
    (W : WeierstrassCurve (closedModelBase S v)) :
    closedModelSubset S v W ⊆ Set.univ :=
  Set.subset_univ _

theorem closedModelConstruct_actual_and_residual
    (W : WeierstrassCurve (closedModelBase S v)) :
    IsClosed (closedModelSubset S v W) ∧
      IsProper (properModelProjectiveStructureMap S v) ∧
      (MissingClosedSubschemeAPIStatement S v W ↔
        Nonempty (MissingClosedSubschemeAPI S v W)) :=
  ⟨closedModelSubset_isClosed S v W,
    ambientProjectiveSpace_isProper S v,
    missingClosedSubschemeAPIStatement_iff S v W⟩

theorem closedModelSubset_isClosed_compl_open
    (W : WeierstrassCurve (closedModelBase S v)) :
    IsOpen (closedModelSubset S v W)ᶜ :=
  (closedModelSubset_isClosed S v W).isOpen_compl

theorem closedModelSubset_eq_univ_iff
    (W : WeierstrassCurve (closedModelBase S v)) :
    closedModelSubset S v W = Set.univ ↔
      ∀ P : ProjectiveClosedModelSpectrum S v,
        closedModelPolynomial S v W ∈ P.asHomogeneousIdeal :=
  by
  constructor
  · intro h P
    rw [← mem_closedModelSubset_iff]
    simp [h]
  · intro h
    ext P
    simp [mem_closedModelSubset_iff, h P]

theorem closedModelSubset_empty_iff
    (W : WeierstrassCurve (closedModelBase S v)) :
    closedModelSubset S v W = ∅ ↔
      ∀ P : ProjectiveClosedModelSpectrum S v,
        closedModelPolynomial S v W ∉ P.asHomogeneousIdeal :=
  by
  constructor
  · intro h P hp
    have : P ∈ closedModelSubset S v W := (mem_closedModelSubset_iff S v W P).mpr hp
    simp [h] at this
  · intro h
    ext P
    simp [mem_closedModelSubset_iff, h P]

theorem closedModelSubset_vanishingIdeal_le
    (W : WeierstrassCurve (closedModelBase S v)) :
    (closedModelVanishingIdeal S v W : HomogeneousIdeal (closedModelGrading S v)) ≤
      HomogeneousIdeal.span {closedModelPolynomial S v W} :=
  by
  rw [ProjectiveSpectrum.vanishingIdeal_le_iff]
  intro P hP
  exact (mem_closedModelSubset_iff S v W P).mp hP

theorem closedModelSubset_isClosed_consumer
    (M : SourcePsiIntegralModelData S v) :
    IsClosed (closedModelSubset S v M.curve) :=
  closedModelSubset_isClosed S v M.curve

theorem closedModelCloseds_eq_closedModelSubset
    (W : WeierstrassCurve (closedModelBase S v)) :
    (closedModelCloseds S v W : Set (ProjectiveClosedModelSpectrum S v)) =
      closedModelSubset S v W :=
  rfl

structure ClosedSubschemeConstructionRequirements
    (W : WeierstrassCurve (closedModelBase S v)) where
  gradedQuotient : Type u
  gradedQuotient_gradedRing : Prop
  projOfQuotient : Scheme.{u}
  closedImmersion : projOfQuotient ⟶ properModelProjectiveSpace S v
  closedImmersion_isClosed : IsClosedImmersion closedImmersion
  support_eq : Prop
  regular : Prop
  componentComparison : Prop

def ClosedSubschemeConstructionRequirementsStatement
    (W : WeierstrassCurve (closedModelBase S v)) : Prop :=
  Nonempty (ClosedSubschemeConstructionRequirements S v W)

theorem closedSubschemeConstructionRequirementsStatement_iff
    (W : WeierstrassCurve (closedModelBase S v)) :
    ClosedSubschemeConstructionRequirementsStatement S v W ↔
      Nonempty (ClosedSubschemeConstructionRequirements S v W) :=
  Iff.rfl

theorem closedSubschemeConstructionRequirements_immersion
    (W : WeierstrassCurve (closedModelBase S v))
    (R : ClosedSubschemeConstructionRequirements S v W) :
    IsClosedImmersion R.closedImmersion :=
  R.closedImmersion_isClosed

theorem closedSubschemeConstructionRequirements_regular
    (W : WeierstrassCurve (closedModelBase S v))
    (R : ClosedSubschemeConstructionRequirements S v W) :
    R.regular := R.regular

/-- Package of the actual closed subset/vanishing-ideal data and the exact
missing closed-subscheme API. -/
structure ProjectiveClosedModelConstructData
    (M : SourcePsiIntegralModelData S v) where
  closedSet : Closeds (ProjectiveClosedModelSpectrum S v)
  closedSet_eq : closedSet = closedModelCloseds S v M.curve
  vanishingIdeal : HomogeneousIdeal (closedModelGrading S v)
  vanishingIdeal_eq : vanishingIdeal = closedModelVanishingIdeal S v M.curve
  ambientProper : IsProper (properModelProjectiveStructureMap S v)
  missingSubscheme : Prop
  missingRegularity : Prop
  missingComponents : Prop

noncomputable def projectiveClosedModelConstructData
    (M : SourcePsiIntegralModelData S v) :
    ProjectiveClosedModelConstructData S v M where
  closedSet := closedModelCloseds S v M.curve
  closedSet_eq := rfl
  vanishingIdeal := closedModelVanishingIdeal S v M.curve
  vanishingIdeal_eq := rfl
  ambientProper := properModelProjectiveSpace_isProper S v
  missingSubscheme := MissingClosedSubschemeAPIStatement S v M.curve
  missingRegularity := ClosedSubschemeConstructionRequirementsStatement S v M.curve
  missingComponents := ClosedSubschemeConstructionRequirementsStatement S v M.curve

theorem projectiveClosedModelConstructData_closedSet
    (M : SourcePsiIntegralModelData S v) :
    (projectiveClosedModelConstructData S v M).closedSet =
      closedModelCloseds S v M.curve :=
  rfl

theorem projectiveClosedModelConstructData_vanishingIdeal
    (M : SourcePsiIntegralModelData S v) :
    (projectiveClosedModelConstructData S v M).vanishingIdeal =
      closedModelVanishingIdeal S v M.curve :=
  rfl

theorem projectiveClosedModelConstructData_ambientProper
    (M : SourcePsiIntegralModelData S v) :
    (projectiveClosedModelConstructData S v M).ambientProper :=
  properModelProjectiveSpace_isProper S v

theorem projectiveClosedModelConstructData_missingSubscheme
    (M : SourcePsiIntegralModelData S v) :
    (projectiveClosedModelConstructData S v M).missingSubscheme =
      MissingClosedSubschemeAPIStatement S v M.curve :=
  rfl

theorem projectiveClosedModelConstructData_missingRegularity
    (M : SourcePsiIntegralModelData S v) :
    (projectiveClosedModelConstructData S v M).missingRegularity =
      ClosedSubschemeConstructionRequirementsStatement S v M.curve :=
  rfl

theorem projectiveClosedModelConstructData_missingComponents
    (M : SourcePsiIntegralModelData S v) :
    (projectiveClosedModelConstructData S v M).missingComponents =
      ClosedSubschemeConstructionRequirementsStatement S v M.curve :=
  rfl

end LeanFormal.IUT.SourcePsiProjectiveClosedModelConstruct
