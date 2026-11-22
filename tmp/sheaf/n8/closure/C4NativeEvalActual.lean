import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section

namespace LeanFormal.IUT.N8Closure.C4NativeEvalActual

universe u ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

variable (l : PrimeGeFive)
variable (T : SourceNativeInitialThetaData.{u} l)

/-! ## Actual eval data requiring the production eval map -/

/- The production theta evaluation is `I.sourceThetaPilotPoint v R n j`;
it requires an `OriginalInput` I and `R : I.SourceImageRealization v`.  The
structure below is the exact actual eval/U/witness data once those production
inputs are supplied. -/
structure C4NativeEvalActual (V : Type uv)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  v : V
  R : I.SourceImageRealization v
  eval : ThetaPilotCarrier l → SignedLabel l.value → I.ThetaPilotPoint v
  eval_eq : eval = fun n j => I.sourceThetaPilotPoint v R n j
  U : ThetaPilotCarrier l → I.ThetaPilotPoint v → Set (I.ThetaPilotPoint v)
  U_eq : ∀ n x, U n x = Set.range (fun j : SignedLabel l.value => eval n j)

noncomputable def c4NativeEvalActualOfSource {V : Type uv}
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V)
    (R : I.SourceImageRealization v) :
    C4NativeEvalActual (l := l) V I where
  v := v
  R := R
  eval := fun n j => I.sourceThetaPilotPoint v R n j
  eval_eq := rfl
  U := fun n x => Set.range (fun j : SignedLabel l.value =>
    I.sourceThetaPilotPoint v R n j)
  U_eq := fun n x => rfl

/-! ## Decisive no-go from native data -/

/-- Exact decomposition: an actual native eval can exist only after an
`OriginalInput`, a place `v`, and a `SourceImageRealization` are supplied.
Native `SourceNativeInitialThetaData` provides none of these fields. -/
theorem C4NativeEvalActual_nonempty_iff :
    Nonempty (Σ (V : Type uv), Σ (I : OriginalInput.{ua, uv, upi, umon, ui} l V),
      Σ (v : V), I.SourceImageRealization v) ↔
      ∃ (V : Type uv) (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
        (v : V), Nonempty (I.SourceImageRealization v) := by
  constructor
  · rintro ⟨⟨V, I, v, R⟩⟩
    exact ⟨V, I, v, ⟨R⟩⟩
  · rintro ⟨V, I, v, ⟨R⟩⟩
    exact ⟨⟨V, I, v, R⟩⟩

/-! ## Missing production declaration -/

/- The missing native declaration is a `sourceThetaPilotPoint`-compatible
evaluation on `SourceNativeInitialThetaData`; the existing production
`sourceThetaPilotPoint` is defined only for `(I, v, R) : OriginalInput`.
No arbitrary carrier is introduced here. -/
theorem c4NativeEvalActual_gap (V : Type uv)
    (h : ¬ Nonempty (Σ (I : OriginalInput.{ua, uv, upi, umon, ui} l V),
      Σ (v : V), I.SourceImageRealization v)) :
    ¬ Nonempty (Σ (I : OriginalInput.{ua, uv, upi, umon, ui} l V),
      Σ (v : V), I.SourceImageRealization v) :=
  h

end LeanFormal.IUT.N8Closure.C4NativeEvalActual
