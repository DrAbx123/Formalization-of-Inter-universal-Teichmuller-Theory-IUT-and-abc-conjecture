import tmp.sheaf.xif.paper.RelativeNormCompletion
import Mathlib.RingTheory.Norm.Basic

/-! # CONDITIONAL STATUS (xi-f)

Only the base q value and q != 0 are actual. The relative-norm contraction law NativeQRelativeNormContraction is missing; no full FinitePlaceQCandidate.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-! # Unconditional base q construction from the relative norm

RelativeNormCompletion constructs the actual relative norm map

  relativeNormCompletion : Completion (nativeFPlaceOverBad X) ->
    Completion (nativeBadBasePlace X).

This file constructs the base q as the relative norm of nativeQActual and proves
it is nonzero using the field-norm zero criterion.  The contraction law
(valuation < 1) is not derivable from the available norm formula and remains
the exact missing norm-evaluation theorem.

No arbitrary q/axiom/sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.BaseQUnconditionalActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The base q value: the actual relative norm of the native q. -/
noncomputable def baseQValue : NativeBaseCompletion (X := X) :=
  relativeNormCompletion (X := X) (nativeQActual X).q

/-- The base q value is nonzero because the relative norm is a field norm and
the native q is nonzero. -/
theorem baseQValue_ne_zero : baseQValue (X := X) ≠ 0 := by
  -- The raw norm is nonzero by the field-norm zero criterion.  The final cast
  -- along the actual place equality preserves nonzeroness.
  have hraw : relativeNormRaw (X := X) (nativeQActual X).q ≠ 0 := by
    unfold relativeNormRaw
    letI := relativeCompletionAlgebra (X := X)
    haveI : Module.Free (NativeBaseCompletionRaw (X := X))
        (NativeFCompletion (X := X)) := inferInstance
    haveI : Module.Finite (NativeBaseCompletionRaw (X := X))
        (NativeFCompletion (X := X)) :=
      relativeCompletionModuleFinite (X := X)
    exact Algebra.norm_ne_zero_iff.mpr (nativeQActual X).q_ne_zero
  intro h
  let e := congrArg (fun p : NumberField.FinitePlace X.S.arithmetic.Fmod =>
      NumberFieldFinitePlace.Completion p) (nativeFPlaceOverBad_comap X)
  have hbase : baseQValue (X := X) =
      cast e (relativeNormRaw (X := X) (nativeQActual X).q) := by
    rw [baseQValue, RelativeNormCompletion.relativeNormCompletion_apply]
  have h0 : cast e (relativeNormRaw (X := X) (nativeQActual X).q) = 0 := by
    rw [← hbase]
    exact h
  have hinj : Function.Injective (cast e) := by
    intro a b hab
    have := congrArg (cast e.symm) hab
    simpa using this
  have h0raw :
      cast e (relativeNormRaw (X := X) (nativeQActual X).q) =
        cast e (0 : NativeBaseCompletionRaw (X := X)) := by
    cases e
    simpa using h0
  have hraw0 : relativeNormRaw (X := X) (nativeQActual X).q = 0 :=
    hinj h0raw
  exact hraw hraw0

/-- Partial base q object: the actual q value and its nonzero law.  The full
FinitePlaceQCandidate additionally needs valuation < 1. -/
structure BaseQPartial where
  q : NativeBaseCompletion (X := X)
  q_ne_zero : q ≠ 0

/-- The unconditional partial base q from the actual relative norm. -/
noncomputable def baseQPartial : BaseQPartial (X := X) where
  q := baseQValue (X := X)
  q_ne_zero := baseQValue_ne_zero (X := X)

/-- The exact missing contraction law for the relative norm of the native q. -/
def NativeQRelativeNormContraction : Prop :=
  (Valued.v (baseQValue (X := X)) : WithZero (Multiplicative Int)) < 1

/-- Full base q candidate from the partial object plus the missing contraction
law. -/
noncomputable def baseQCandidateOfPartial
    (P : BaseQPartial (X := X))
    (hcontraction :
      (Valued.v P.q : WithZero (Multiplicative Int)) < 1) :
    FinitePlaceQCandidate (nativeBadBasePlace X) where
  q := P.q
  q_ne_zero := P.q_ne_zero
  valuation_lt_one := hcontraction

/-- Applying the conditional candidate to the actual relative norm q. -/
noncomputable def baseQCandidateOfContraction
    (h : NativeQRelativeNormContraction (X := X)) :
    FinitePlaceQCandidate (nativeBadBasePlace X) :=
  baseQCandidateOfPartial (X := X) (baseQPartial (X := X)) h

/-- The constructed q is the actual relative norm of nativeQActual. -/
@[simp] theorem baseQCandidateOfContraction_q
    (h : NativeQRelativeNormContraction (X := X)) :
    (baseQCandidateOfContraction (X := X) h).q = baseQValue (X := X) := rfl

/-! ## Exact missing norm evaluation

The actual nonzero base q is constructed unconditionally:
baseQValue = relativeNormCompletion (nativeQActual X).q, with q_ne_zero proved
by Algebra.norm_ne_zero_iff.

The full FinitePlaceQCandidate needs the single missing contraction law

  NativeQRelativeNormContraction :=
    (Valued.v baseQValue : WithZero (Multiplicative Int)) < 1.

This is the exact missing local norm-evaluation theorem for the Tate q: the
available norm transport is base -> extension, and no local norm absolute-value
formula for the relative norm on completions is present. -/

end LeanFormal.IUT.XiFPaper.BaseQUnconditionalActual

end
