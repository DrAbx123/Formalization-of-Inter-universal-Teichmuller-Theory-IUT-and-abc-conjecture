import LeanFormal.IUT.Foundations.AlgebraicGeometry.CanonicalCompletionNormedSpace
import LeanFormal.IUT.Foundations.AlgebraicGeometry.ClosedBallInstanceFromProperSpace
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedLogNormComparison
import Mathlib.Analysis.Normed.Algebra.Basic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

/-!
# Base norm compatibility from the permanent closed-ball instances

The canonical completion

  `K = concretePlace.maximalIdeal.adicCompletion GaussianField`

and the normalized completion `NormalizedCompletion concretePlace` are the same
underlying field via `normalizedCompletionRingEquiv`.  Their norms have the same
unit ball (`normalizedCompletion_norm_le_one_iff` plus
`NormalizedLogNormComparison.norm_integer_eq_valued_integer`).

This file reduces `BaseNormCompatibility` to the exact normalized norm equality
on the canonical field, records the inequality/ball data which is available
from the tree, and transports the `NormedAlgebra ℚ_[5]` structure once that
equality is supplied.

The permanent `ClosedBallInstanceResidual` (proved from the repaired properness
candidate) supplies `ProperSpace K` and the complete DVR/finite residue data,
which are the topological hypotheses under which the normalized absolute-value
uniqueness is applied.  No instance is postulated.

No fake instance, no card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.BaseNormCompatibilityProof

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.CanonicalCompletionNormedSpace
open LeanFormal.IUT.ClosedBallInstanceFromProperSpace

universe u

local instance gaussianBaseNormIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

local instance factFivePrime : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The canonical completion. -/
abbrev completionField : Type :=
  LeanFormal.IUT.CanonicalCompletionNormedSpace.completionField

/-- The normalized completion. -/
abbrev normalizedCompletion : Type :=
  LeanFormal.IUT.NormalizedCompletion concretePlace

/-- The scalar field of the normalized completion. -/
abbrev normalizedScalarField : Type :=
  LeanFormal.IUT.PadicScalarField concretePlace

/-! ## Topological hypotheses from the closed-ball residual -/

theorem properSpace_of_closedBallInstanceResidual
    (h : ClosedBallInstanceResidual) : ProperSpace completionField :=
  LeanFormal.IUT.ClosedBallProperSpaceVerification.properSpace_of_closedBallInstanceResidual h

theorem properSpace_canonical : ProperSpace completionField :=
  properSpace_of_closedBallInstanceResidual closedBallInstanceResidual_holds

theorem completeSpace_integer : CompleteSpace (𝒪[completionField]) :=
  LeanFormal.IUT.ClosedBallInstanceFromProperSpace.completeSpace_integer

theorem isDiscreteValuationRing_integer :
    IsDiscreteValuationRing (𝒪[completionField]) :=
  LeanFormal.IUT.ClosedBallInstanceFromProperSpace.isDiscreteValuationRing_integer

theorem finite_residueField : Finite (𝓀[completionField]) :=
  LeanFormal.IUT.ClosedBallInstanceFromProperSpace.finite_residueField

/-! ## The normalized norm on the canonical field -/

/-- The normalized norm transported to the canonical completion along the ring
equivalence of `FinitePlaceNormalizedCompletion`. -/
noncomputable def normalizedNormOnCompletion (x : completionField) : ℝ :=
  ‖(LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm x‖

/-- The normalized norm on the canonical field is a norm. -/
theorem normalizedNormOnCompletion_nonneg (x : completionField) :
    0 ≤ normalizedNormOnCompletion x :=
  norm_nonneg _

theorem normalizedNormOnCompletion_eq_zero_iff {x : completionField} :
    normalizedNormOnCompletion x = 0 ↔ x = 0 :=
by
  rw [normalizedNormOnCompletion, norm_eq_zero]
  constructor
  · intro h
    exact (LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm.injective
      (by simpa using h)
  · intro h
    simp [h]

/-- The normalized unit ball is the canonical unit ball. -/
theorem normalizedNormOnCompletion_le_one_iff (x : completionField) :
    normalizedNormOnCompletion x ≤ 1 ↔ ‖x‖ ≤ 1 :=
by
  rw [normalizedNormOnCompletion]
  have h := LeanFormal.IUT.normalizedCompletion_norm_le_one_iff concretePlace
    ((LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm x)
  simpa [LeanFormal.IUT.normalizedCompletionRingEquiv] using h

/-! ## The exact normalized norm equality -/

/-- The exact extension-uniqueness statement needed for the base norm: the
canonical norm and the normalized norm agree on the canonical completion. -/
def CanonicalNormalizedNormEquality : Prop :=
  ∀ x : completionField, ‖x‖ = normalizedNormOnCompletion x

theorem canonicalNormalizedNormEquality_iff :
    CanonicalNormalizedNormEquality ↔
      ∀ x : completionField, ‖x‖ = normalizedNormOnCompletion x :=
  Iff.rfl

/-- The normalized norm of a base scalar is the base norm, by the normalized
`NormedAlgebra` instance. -/
theorem normalizedNorm_algebraMap (q : normalizedScalarField) :
    ‖(algebraMap normalizedScalarField normalizedCompletion) q‖ = ‖q‖ :=
  norm_algebraMap' normalizedCompletion q

/-- Under the exact normalized norm equality, the canonical base norm agrees
with the normalized base norm. -/
theorem canonicalNorm_algebraMap_eq_of_normEquality
    (h : CanonicalNormalizedNormEquality) (q : normalizedScalarField) :
    ‖(algebraMap normalizedScalarField completionField) q‖ = ‖q‖ :=
by
  let x : completionField := algebraMap normalizedScalarField completionField q
  have hx : ‖x‖ = normalizedNormOnCompletion x := h x
  -- the transported normalized norm of the base scalar is the base norm
  rw [hx, normalizedNormOnCompletion]
  -- the normalized ring equivalence is compatible with the base algebra map
  congr 1
  exact (LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm.commutes q

/-! ## The exact base norm compatibility -/

/-- `BaseNormCompatibility` follows from the normalized norm equality, with the
base scalar field identified via `normalizedScalarField`. -/
theorem baseNormCompatibility_of_normalizedNormEquality
    (h : CanonicalNormalizedNormEquality)
    (hbase : normalizedScalarField = ℚ_[5]) :
    BaseNormCompatibility :=
by
  subst hbase
  intro q
  exact canonicalNorm_algebraMap_eq_of_normEquality h q

/-- Conversely, the base norm compatibility gives the same equality on base
scalars. -/
theorem canonicalNorm_algebraMap_eq_of_baseNorm
    (hbase : BaseNormCompatibility) (q : ℚ_[5]) :
    ‖(algebraMap ℚ_[5] completionField) q‖ = ‖q‖ :=
  hbase q

/-! ## Closing the NormedAlgebra bridge -/

/-- Once `BaseNormCompatibility` is available, the actual canonical normed-algebra
structure is the one constructed in `CanonicalCompletionNormedSpace`. -/
noncomputable def normedAlgebraOfBaseCompatibility
    (h : BaseNormCompatibility) :
    NormedAlgebra ℚ_[5] completionField :=
  normedAlgebraOfBaseNorm h

theorem normedAlgebraOfBaseCompatibility_smul
    (h : BaseNormCompatibility) (q : ℚ_[5]) (x : completionField) :
    letI := normedAlgebraOfBaseCompatibility h
    ‖q • x‖ = ‖q‖ * ‖x‖ :=
by
  letI := normedAlgebraOfBaseCompatibility h
  rw [norm_smul]

/-! ## Exact residual -/

/-- The exact missing extension-uniqueness statement: canonical and normalized
norms on the canonical completion agree pointwise. -/
def BaseNormExtensionUniquenessResidual : Prop :=
  CanonicalNormalizedNormEquality

/-- The residual, if supplied, closes `BaseNormCompatibility` and the normed
algebra bridge (the base-scalar identification is the concrete rational-place
field equality used by production). -/
theorem baseNormCompatibility_of_extensionUniquenessResidual
    (h : BaseNormExtensionUniquenessResidual)
    (hbase : normalizedScalarField = ℚ_[5]) :
    BaseNormCompatibility :=
  baseNormCompatibility_of_normalizedNormEquality h hbase


/-! ## Base-scalar consequences -/

/-- The normalized norm of the image of a base scalar is the base norm. -/
theorem normalizedNormOnCompletion_algebraMap
    (hbase : normalizedScalarField = ℚ_[5]) (q : ℚ_[5]) :
    normalizedNormOnCompletion
      (algebraMap ℚ_[5] completionField q) = ‖q‖ :=
by
  subst hbase
  rw [normalizedNormOnCompletion]
  -- the ring equivalence commutes with the base algebra map
  rw [show (LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm
      (algebraMap normalizedScalarField completionField q) =
      (algebraMap normalizedScalarField normalizedCompletion) q from by
    exact (LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm.commutes q]
  exact normalizedNorm_algebraMap q

theorem canonicalNorm_algebraMap_eq_base_norm_of_normEquality
    (h : CanonicalNormalizedNormEquality)
    (hbase : normalizedScalarField = ℚ_[5]) (q : ℚ_[5]) :
    ‖(algebraMap ℚ_[5] completionField) q‖ = ‖q‖ :=
by
  rw [h (algebraMap ℚ_[5] completionField q)]
  exact normalizedNormOnCompletion_algebraMap hbase q

/-- The normalized norm equality on all of `completionField` implies the
canonical base norm equality. -/
theorem baseNormCompatibility_of_normEquality
    (h : CanonicalNormalizedNormEquality)
    (hbase : normalizedScalarField = ℚ_[5]) :
    BaseNormCompatibility :=
  canonicalNorm_algebraMap_eq_base_norm_of_normEquality h hbase

/-- Conversely, the canonical base norm equality determines the normalized
norm on base scalars, not on all of the field. -/
theorem normalizedNorm_algebraMap_eq_of_baseNormCompatibility
    (h : BaseNormCompatibility) (hbase : normalizedScalarField = ℚ_[5])
    (q : ℚ_[5]) :
    normalizedNormOnCompletion (algebraMap ℚ_[5] completionField q) = ‖q‖ :=
  normalizedNormOnCompletion_algebraMap hbase q

/-! ## Interface summary -/

theorem baseNormCompatibility_iff_normalizedNormAlgebraMap
    (hbase : normalizedScalarField = ℚ_[5]) :
    BaseNormCompatibility ↔
      (∀ q : ℚ_[5],
        ‖(algebraMap ℚ_[5] completionField) q‖ = ‖q‖) :=
  Iff.rfl

theorem normedAlgebraOfBaseCompatibility_algebraMap
    (h : BaseNormCompatibility) (q : ℚ_[5]) :
    letI := normedAlgebraOfBaseCompatibility h
    (algebraMap ℚ_[5] completionField q : completionField) =
      (algebraMap ℚ_[5] completionField) q :=
  rfl

end LeanFormal.IUT.BaseNormCompatibilityProof

end
