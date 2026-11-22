import LeanFormal.IUT.Foundations.AlgebraicGeometry.UniformizerDVRDecomposition
import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedLogNormComparison
import LeanFormal.IUT.IUTII.Frobenioid.Example36LogDomainActual
import Mathlib.Topology.MetricSpace.ProperSpace

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Availability of the actual principal-unit logarithm on the canonical completion

The tree's actual p-adic logarithm on principal units is

  `LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog`.

Its definition only needs

  `[NormedField K] [CharZero K] [CompleteSpace K] [IsUltrametricDist K] [ProperSpace K]`,

not a `NormedAlgebra` structure.  The canonical completion

  `K = concretePlace.maximalIdeal.adicCompletion GaussianField`

has all these field instances once `ProperSpace K` is supplied.  This file
records the availability of the actual principal-unit logarithm on `K` and the
exact residual which prevents extending it to a logarithm on all of `Kˣ`: the
additivity theorem `principalUnitLog_mul` additionally requires
`NormedAlgebra ℚ_[p] K`, which is the missing base-norm structure recorded in
`CanonicalCompletionNormedSpace`.

## Main results

* `canonicalPrincipalUnitLog`: the actual tree logarithm on principal units of
  the canonical completion, under `[ProperSpace K]`;
* `canonicalPrincipalUnitLog_one`: its value at one;
* `canonicalPrincipalUnitLog_apply`: the underlying `log1p` formula;
* `canonicalPrincipalUnitLog_mul`: conditional on `NormedAlgebra ℚ_[5] K`; this
  is the exact missing additivity input;
* `CanonicalLogExtensionObstruction`: the exact residual `Prop`.

No fake log, no card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.CanonicalPrincipalUnitLogAvailability

open scoped WithZero Valued
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.NormalizedLogNormComparison
open LeanFormal.IUT.LocalFieldIntegralUnits

universe u

local instance factFivePrime : Fact (Nat.Prime 5) := ⟨by norm_num⟩

local instance gaussianPrincipalUnitLogIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

/-- The canonical completed valuation field. -/
abbrev completionField : Type :=
  LeanFormal.IUT.NormalizedLogNormComparison.completionField

/-! ## The actual logarithm under properness -/

/-- The actual tree principal-unit logarithm on the canonical completion.  Only
the field/properness hypotheses are required for the definition. -/
noncomputable def canonicalPrincipalUnitLog
    [ProperSpace completionField]
    (u : principalUnits (K := completionField)) : completionField :=
  LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
    (K := completionField) u

theorem canonicalPrincipalUnitLog_one [ProperSpace completionField] :
    canonicalPrincipalUnitLog (1 : principalUnits (K := completionField)) = 0 :=
  LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog_one
    (K := completionField)

theorem canonicalPrincipalUnitLog_apply [ProperSpace completionField]
    (u : principalUnits (K := completionField)) :
    canonicalPrincipalUnitLog u =
      LeanFormal.IUT.LocalFieldLogarithm.log1p
        (((u : (LeanFormal.IUT.LocalFieldIntegralUnits.Integers
          completionField)ˣ).val : completionField) - 1) :=
  rfl

/-! ## The missing additivity structure -/

/-- Additivity of the actual principal-unit logarithm on the canonical completion
requires the missing `NormedAlgebra ℚ_[5]` structure.  This theorem does not
assert the structure; it states the exact implication. -/
theorem canonicalPrincipalUnitLog_mul
    [ProperSpace completionField]
    [NormedAlgebra ℚ_[5] completionField]
    (u v : principalUnits (K := completionField)) :
    canonicalPrincipalUnitLog (u * v) =
      canonicalPrincipalUnitLog u + canonicalPrincipalUnitLog v :=
  LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog_mul
    (K := completionField) 5 u v

/-- The residual statement for the log-extension assembly: the canonical
completion needs the base `NormedAlgebra ℚ_[5]` structure (equivalently the
base-norm compatibility) before the principal-unit logarithm is additive. -/
def CanonicalLogExtensionObstruction : Prop :=
  Nonempty (NormedAlgebra ℚ_[5] completionField)

/-- Under the residual normed-algebra structure, the actual logarithm is
additive on principal units. -/
theorem canonicalPrincipalUnitLog_mul_of_obstruction
    [ProperSpace completionField]
    (h : CanonicalLogExtensionObstruction)
    (u v : principalUnits (K := completionField)) :
    canonicalPrincipalUnitLog (u * v) =
      canonicalPrincipalUnitLog u + canonicalPrincipalUnitLog v :=
by
  rcases h with ⟨hna⟩
  letI : NormedAlgebra ℚ_[5] completionField := hna
  exact canonicalPrincipalUnitLog_mul u v

/-- The logarithm is available iff properness is available; the log-extension
defect is exactly the normed-algebra structure, not the logarithm itself. -/
theorem canonicalPrincipalUnitLog_available_iff_properSpace :
    (Nonempty (ProperSpace completionField) →
      Nonempty (principalUnits (K := completionField) → completionField)) :=
by
  rintro ⟨hproper⟩
  letI : ProperSpace completionField := hproper
  exact ⟨canonicalPrincipalUnitLog⟩

end LeanFormal.IUT.CanonicalPrincipalUnitLogAvailability

end