import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedLogNormComparison
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# The canonical completion normed-space structure (L0.4 A/C batch)

This file isolates the exact base-field norm compatibility needed to put a
`NormedSpace ℚ_[5]` / `NormedAlgebra ℚ_[5]` structure on the canonical adic
completion

  `K = concretePlace.maximalIdeal.adicCompletion GaussianField`.

The production `completionAlgebra` already gives `Algebra ℚ_[5] K` (through the
lower completion at the rational place 5).  What is missing for the
`NormedAlgebra` instance is the compatibility of the canonical completion norm
with the base norm:

  `‖algebraMap ℚ_[5] K q‖ = ‖q‖`  for all `q : ℚ_[5]`.

This is the base-field case of the absolute-value extension problem.  At the
concrete place the relative residue degree is one, so the canonical log-norm
formula predicts the compatibility; the file records the exact reduction and
does not postulate the missing equality as a fake instance.

## What is proved here

* `canonicalBaseAlgebra`: the actual `Algebra ℚ_[5] K` from production;
* `BaseNormCompatibility`: the exact missing equality;
* `normedAlgebraOfBaseNorm`: constructs the normed-algebra structure from the
  compatibility equality (this is a reduction, not an inhabitant of the missing
  equality);
* `normedSpaceOfBaseNorm`, `normedSpaceCanonicalCompletion`: the corresponding
  `NormedSpace` consumers;
* `baseNormCompatibility_iff_norm_algebraMap`: the equivalence between the
  compatibility and the `norm_algebraMap` identity;
* `normedAlgebraCanonicalCompletion_iff_baseNorm`: an exact equivalence between
  the existence of a normed-algebra structure and the compatibility equality;
* residual section: if no proof of the compatibility is available, the exact
  missing statement is recorded.

No fake instance, no card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.CanonicalCompletionNormedSpace

open scoped WithZero Valued
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.NormalizedLogNormComparison

universe u

local instance gaussianCanonicalNormedSpaceIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

/-- The canonical completed valuation field at the concrete Gaussian place. -/
abbrev completionField : Type :=
  LeanFormal.IUT.NormalizedLogNormComparison.completionField

/-! ## The actual base algebra -/

/-- The actual `Algebra ℚ_[5] K` structure induced by the lower completion at
the rational place 5.  The lower completion is definitionally `ℚ_[5]` in the
concrete split case. -/
noncomputable def canonicalBaseAlgebra : Algebra ℚ_[5] completionField :=
  completionAlgebra (k := ℚ) concretePlace

/-- The canonical completion norm is compatible with the base norm.  This is the
exact missing absolute-value-extension equality for the concrete completion. -/
def BaseNormCompatibility : Prop :=
  ∀ q : ℚ_[5],
    ‖(algebraMap ℚ_[5] completionField) q‖ = ‖q‖

/-- The compatibility equality is the same as the standard `norm_algebraMap`
identity for the canonical base algebra. -/
theorem baseNormCompatibility_iff_norm_algebraMap :
    BaseNormCompatibility ↔
      ∀ q : ℚ_[5],
        ‖(algebraMap ℚ_[5] completionField) q‖ = ‖q‖ := by
  rfl

/-! ## Constructing the normed algebra from the base compatibility -/

/-- A `NormedAlgebra ℚ_[5] K` structure is obtained from the actual base algebra
and the base-norm compatibility.  This is a construction conditional on the
missing compatibility, not an inhabitant of it. -/
noncomputable def normedAlgebraOfBaseNorm
    (hbase : BaseNormCompatibility) :
    NormedAlgebra ℚ_[5] completionField where
  toAlgebra := canonicalBaseAlgebra
  norm_smul_le q x := by
    rw [Algebra.smul_def]
    rw [norm_mul, hbase q]
    exact le_rfl

/-- The induced `NormedSpace` structure. -/
noncomputable def normedSpaceOfBaseNorm
    (hbase : BaseNormCompatibility) :
    NormedSpace ℚ_[5] completionField :=
  (normedAlgebraOfBaseNorm hbase).toNormedSpace

/-- A `NormedSpace` consumer form; the normed-algebra construction already
provides the stronger structure. -/
theorem normedSpaceCanonicalCompletion_of_baseNorm
    (hbase : BaseNormCompatibility) :
    Nonempty (NormedSpace ℚ_[5] completionField) :=
  ⟨normedSpaceOfBaseNorm hbase⟩

/-! ## Reverse direction: normed structure gives base compatibility -/

/-- A normed-algebra structure on the canonical completion forces the base-norm
compatibility.  This is the standard `norm_algebraMap'` identity. -/
theorem baseNormCompatibility_of_normedAlgebra
    (h : NormedAlgebra ℚ_[5] completionField) :
    BaseNormCompatibility :=
by
  letI := h
  intro q
  exact norm_algebraMap' completionField q

/-- Exact equivalence: the missing base-norm compatibility is equivalent to the
existence of the normed-algebra structure on the canonical completion. -/
theorem normedAlgebraCanonicalCompletion_iff_baseNorm :
    Nonempty (NormedAlgebra ℚ_[5] completionField) ↔
      BaseNormCompatibility :=
by
  constructor
  · rintro ⟨h⟩
    exact baseNormCompatibility_of_normedAlgebra h
  · intro hbase
    exact ⟨normedAlgebraOfBaseNorm hbase⟩

/-- The induced finite-dimensional properness reduction: once the base
compatibility is supplied, the canonical completion is a proper normed space
via the production finite-dimensionality theorem. -/
theorem properSpaceCanonicalCompletion_of_baseNorm
    (hbase : BaseNormCompatibility)
    (hfin : Module.Finite ℚ_[5] completionField) :
    ProperSpace completionField :=
by
  letI := normedSpaceOfBaseNorm hbase
  exact FiniteDimensional.proper ℚ_[5] completionField

/-! ## Relation to the concrete residue degree -/

/-- At the concrete Gaussian place the relative residue degree is one; this is
the arithmetic fact which makes the base-norm compatibility the expected
instance of the canonical log-norm formula. -/
theorem concretePlace_relativeResidueDegree_eq_one :
    LeanFormal.IUT.NumberFieldFinitePlace.relativeResidueDegree
      (k := ℚ) concretePlace = 1 :=
  concreteGaussianFivePlace_relativeResidueDegree_eq_one

/-- The canonical log-norm formula at the concrete place gives, for every
nonzero element, the norm as `absNorm` to the valuation exponent. -/
theorem canonical_norm_eq_absNorm_zpow
    (x : completionField) (hx : x ≠ 0) :
    ‖x‖ = (Ideal.absNorm concretePlace.maximalIdeal.asIdeal : ℝ) ^
      (Multiplicative.toAdd (WithZero.unzero
        (valued_ne_zero_of_ne_zero hx))) :=
  norm_eq_absNorm_zpow concretePlace x hx

/-- The base field `ℚ_[5]` sits in the canonical completion through the actual
algebra map.  The residue-degree-one fact is the arithmetic input that would
turn the canonical formula into the base-norm compatibility; the equality itself
is not proved here. -/
theorem baseNormCompatibility_expected_from_canonical_formula :
    BaseNormCompatibility ↔
      ∀ q : ℚ_[5],
        ‖(algebraMap ℚ_[5] completionField) q‖ = ‖q‖ :=
  baseNormCompatibility_iff_norm_algebraMap

/-! ## Exact residual -/

/-- The remaining source/Mathlib object is the base-norm compatibility
`BaseNormCompatibility` (equivalently a `NormedAlgebra ℚ_[5]` instance on the
canonical adic completion).  It is the concrete, residue-degree-one case of the
absolute-value-extension uniqueness.  No inhabitant of this definition is
provided in this file. -/
def BaseNormCompatibilityResidual : Prop :=
  BaseNormCompatibility

/-- If the residual base-norm compatibility is available, the canonical
completion receives the normed algebra and normed space structures. -/
theorem normedStructure_of_baseNormCompatibilityResidual
    (h : BaseNormCompatibilityResidual) :
    Nonempty (NormedAlgebra ℚ_[5] completionField) :=
  normedAlgebraCanonicalCompletion_iff_baseNorm.mpr h


/-! ## Normed-space consequences of the base compatibility -/

/-- Under the base compatibility, scalar multiplication is norm-preserving in
the sense of the normed-space inequality, in fact with equality. -/
theorem norm_smul_eq_of_baseNorm
    (hbase : BaseNormCompatibility) (q : ℚ_[5]) (x : completionField) :
    ‖q • x‖ = ‖q‖ * ‖x‖ := by
  rw [Algebra.smul_def, norm_mul, hbase q]

/-- The normed-space inequality required by `ProperSpace`/`FiniteDimensional`
is immediate from the equality form. -/
theorem norm_smul_le_of_baseNorm
    (hbase : BaseNormCompatibility) (q : ℚ_[5]) (x : completionField) :
    ‖q • x‖ ≤ ‖q‖ * ‖x‖ :=
  (norm_smul_eq_of_baseNorm hbase q x).le

/-- The base compatibility is preserved when the base scalar is read through
the canonical algebra map.  This is the form used in finite-dimensional
calculations. -/
theorem norm_algebraMap_eq_of_baseNorm
    (hbase : BaseNormCompatibility) (q : ℚ_[5]) :
    ‖(algebraMap ℚ_[5] completionField) q‖ = ‖q‖ :=
  hbase q

/-- The actual base algebra map is the lower-completion algebra map. -/
theorem algebraMap_eq_baseAlgebra (q : ℚ_[5]) :
    (algebraMap ℚ_[5] completionField) q =
      (canonicalBaseAlgebra).commutes' q := by
  rfl

/-- The `NormedSpace` structure constructed from the base compatibility has the
expected scalar norm action. -/
theorem normedSpaceOfBaseNorm_smul
    (hbase : BaseNormCompatibility) (q : ℚ_[5]) (x : completionField) :
    @NormedSpace.toModule ℚ_[5] completionField _ _
      (normedSpaceOfBaseNorm hbase) q x = q • x :=
  rfl

/-! ## Reduction to the base-norm equality only -/

/-- A `NormedAlgebra` structure is equivalent to the actual base algebra plus
the base-norm compatibility.  This isolates the exact missing absolute-value
statement: no other normed-algebra field is missing. -/
theorem normedAlgebraStructure_iff_baseNorm :
    (∃ _ : NormedAlgebra ℚ_[5] completionField, True) ↔
      BaseNormCompatibility :=
by
  constructor
  · rintro ⟨h, _⟩
    exact baseNormCompatibility_of_normedAlgebra h
  · intro hbase
    exact ⟨normedAlgebraOfBaseNorm hbase, trivial⟩

/-- The reverse direction of the `NormedSpace` reduction: the base-norm
compatibility yields a normed-space structure.  The forward direction would need
the base-norm equality from an arbitrary normed-space structure; that is the same
absolute-value-extension statement and is recorded as residual, not assumed here. -/
theorem normedSpaceStructure_of_baseNorm
    (hbase : BaseNormCompatibility) :
    Nonempty (NormedSpace ℚ_[5] completionField) :=
  ⟨normedSpaceOfBaseNorm hbase⟩
/-! ## Explicit residual forms -/

/-- The exact absolute-value-extension statement for the base field: the
canonical completion norm restricts to the `ℚ_[5]` norm. -/
def BaseNormExtensionStatement : Prop :=
  ∀ q : ℚ_[5],
    ‖(algebraMap ℚ_[5] completionField) q‖ = ‖q‖

theorem baseNormExtensionStatement_iff_compatibility :
    BaseNormExtensionStatement ↔ BaseNormCompatibility :=
  Iff.rfl

/-- The residual statement is precisely the base-field case of uniqueness of
absolute-value extensions.  No inhabitant is provided. -/
theorem baseNormExtensionStatement_residual :
    BaseNormCompatibilityResidual ↔ BaseNormExtensionStatement :=
  Iff.rfl

end LeanFormal.IUT.CanonicalCompletionNormedSpace

end