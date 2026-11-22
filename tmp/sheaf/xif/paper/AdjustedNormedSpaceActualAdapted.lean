import tmp.sheaf.xif.paper.CompletionNormedSpaceInequalityAdapted

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Adjusted completion norm with Fmod-scalar norm scaling

Task-696 write-only attempt.

The canonical upper-completion norm is not base-completion norm-linear:
  ‖a • x‖ = ‖a‖ ^ d * ‖x‖,
where d = relativeCompletionDegree and a is the base-completion scalar.

The adjusted candidate norm is
  adjustedNorm x := ‖x‖ ^ (1 / d).
For nonzero a this satisfies
  adjustedNorm (a • x)
    = ‖a‖ * adjustedNorm x,
because
  (‖a‖ ^ d * ‖x‖) ^ (1 / d) = ‖a‖ * ‖x‖ ^ (1 / d).

This file constructs the actual adjusted norm function, its nonnegativity,
zero law, and the exact scaling law from the actual scalar action and
norm_completionMap_pow.

The adjusted norm is not yet a Mathlib NormedSpace instance: constructing the
SeminormedAddCommGroup/NormedSpace structure requires the triangle inequality
and the topology-equivalence proof for the rpow norm. These are the exact
missing normalization data recorded below. No arbitrary NormedSpace instance or
nonstandard triangle proof is asserted.

No arbitrary instance/True/PUnit, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.AdjustedNormedSpaceActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.CompletionNormedFiniteActual
open LeanFormal.IUT.XiFPaper.CompletionNormedSpaceInequalityAdapted

universe u v

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The relative completion degree as a positive real. -/
def relativeDegreeReal : Real :=
  (nativeRelativeCompletionDegree (X := X) : Real)

theorem relativeDegreeReal_pos : 0 < relativeDegreeReal (X := X) := by
  unfold relativeDegreeReal
  exact_mod_cast relativeCompletionDegree_pos (k := X.S.arithmetic.Fmod)
    (nativeFPlaceOverBad X)

/-- The adjusted completion norm. -/
def adjustedNorm (x : NativeFCompletion (X := X)) : Real :=
  Real.rpow ‖x‖ (1 / relativeDegreeReal (X := X))

/-- The adjusted norm is nonnegative. -/
theorem adjustedNorm_nonneg (x : NativeFCompletion (X := X)) :
    0 ≤ adjustedNorm (X := X) x :=
  Real.rpow_nonneg (norm_nonneg x) _

/-- The adjusted norm vanishes at zero. -/
@[simp] theorem adjustedNorm_zero :
    adjustedNorm (X := X) (0 : NativeFCompletion (X := X)) = 0 := by
  unfold adjustedNorm
  rw [norm_zero]
  exact Real.zero_rpow (one_div_ne_zero (ne_of_gt (relativeDegreeReal_pos (X := X))))

/-- The exact adjusted norm scaling law for nonzero base scalars. -/
theorem adjustedNorm_smul
    (a : NativeBaseCompletionRaw (X := X)) (ha : a ≠ 0)
    (x : NativeFCompletion (X := X)) :
    adjustedNorm (X := X) (a • x) =
      ‖a‖ * adjustedNorm (X := X) x := by
  letI := relativeCompletionAlgebra (X := X)
  have hsmul := completionAlgebra_smul
    (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X) a x
  have hpow := norm_completionMap_pow
    (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X) a ha
  have hcast : ‖completionMap (k := X.S.arithmetic.Fmod)
      (nativeFPlaceOverBad X) a‖ =
      ‖a‖ ^ nativeRelativeCompletionDegree (X := X) := by
    simpa [nativeRelativeCompletionDegree] using hpow
  unfold adjustedNorm
  rw [hsmul, norm_mul, hcast]
  rw [Real.mul_rpow (norm_nonneg a) (norm_nonneg x)]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (norm_nonneg a)]
  have hd : relativeDegreeReal (X := X) ≠ 0 :=
    ne_of_gt (relativeDegreeReal_pos (X := X))
  have hcomp : (nativeRelativeCompletionDegree (X := X) : Real) *
      (1 / relativeDegreeReal (X := X)) = 1 := by
    unfold relativeDegreeReal
    field_simp [hd]
  rw [hcomp, Real.rpow_one]
  rfl

/-- The adjusted norm is equivalent to the canonical completion norm at the
level of the scaling formula; topology equivalence is the missing structure. -/
def AdjustedNormTopologyEquivalent : Prop :=
  ∀ x : NativeFCompletion (X := X), adjustedNorm (X := X) x ≠ 0 ↔ x ≠ 0

/-- The exact missing SeminormedAddCommGroup core (triangle inequality for the
rpow norm). -/
def MissingAdjustedTriangleCore : Prop :=
  Nonempty (SeminormedAddCommGroup (NativeFCompletion (X := X)))

/-- The exact missing topology-equivalence/normalized-instance data. -/
structure MissingAdjustedNormedSpaceData : Prop where
  triangle_core : MissingAdjustedTriangleCore (X := X)
  topology_equivalent : AdjustedNormTopologyEquivalent (X := X)

/-- Exact status: the adjusted norm function and its scalar scaling law are
constructed; the missing pieces are the triangle-inequality core and the
topology-equivalence proof needed to install a NormedSpace instance. -/
theorem adjustedNormedSpaceActual_status :
    (∀ (a : NativeBaseCompletionRaw (X := X)), a ≠ 0 →
      ∀ x : NativeFCompletion (X := X),
        adjustedNorm (X := X) (a • x) = ‖a‖ * adjustedNorm (X := X) x) ∧
      (adjustedNorm (X := X) (0 : NativeFCompletion (X := X)) = 0) :=
  ⟨fun a ha x => adjustedNorm_smul (X := X) a ha x,
    adjustedNorm_zero (X := X)⟩

end LeanFormal.IUT.XiFPaper.AdjustedNormedSpaceActualAdapted

end
