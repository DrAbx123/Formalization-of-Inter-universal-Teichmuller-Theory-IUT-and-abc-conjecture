import tmp.sheaf.xif.paper.S3138SourceProcessionCarrierActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceRoundtripRealizationSpec
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3138: source-level roundtrip realization spec for the actual source core

This file transports the route-2 roundtrip interface
(`StepXI/SourceRoundtripRealizationSpec.lean`) to the *actual source core*
`sourceStepXICore I` of `S3138SourceProcessionCoreActual`.

What is proved (all from the already-proved column-realization lemmas, no new
data):

* on the actual source core, the roundtrip spec is inhabited exactly when the
  canonical column realization `coreColumnRealization` is injective
  (`sourceStepXI_roundtripSpec_nonempty_iff_injective);
* each direction is exported separately
  (`sourceStepXI_roundtripSpec_implies_injective,
  `sourceStepXI_injective_implies_roundtripSpec).

What is NOT proved and is recorded as the exact residual: the source carrier
uses `FiniteColumnIndex = finiteLabel l x finiteLabel l x level` with
`finiteLabel l = ZMod l.value` (finite, torsion) while the source core labels
live in the torsion-free lattice `ZZ x ZZ`.  Every additive homomorphism
`ZMod l.value ->+ ZZ x ZZ` is therefore expected to be zero, which would make
the canonical column realization ignore its two horizontal labels and destroy
injectivity (hence the roundtrip spec) for `l.value >= 5`.  The zero-hom
statement is not formalized here; the residual obligation is
`SourceStepXIColumnReadbackResidual` below.

Source: IUT III, Theorem 3.11 / Remark 3.11.1; IUT II, Corollary 4.10 (ii).
-/

namespace LeanFormal.IUT.XiFPaper.S3138SourceRoundtripRealizationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.SourceColumnRealization
open LeanFormal.IUT.SourceRoundtripRealization
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-- The exact readback residual on the actual source core: existence of a
roundtrip realization spec for the canonical column realization of
`sourceStepXICore I` at a supplied label homomorphism. -/
def SourceStepXIColumnReadbackResidual
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (N : Nat)
    (φ : ConcreteFiniteTheorem311.finiteLabel l →+ (ℤ × ℤ))
    (c₀ : SourceStepXIChoice I) : Prop :=
  Nonempty (RoundtripRealizationSpec (N := N) (sourceStepXICore I) φ c₀)

/-- The roundtrip spec is inhabited exactly when the canonical column
realization of the actual source core is injective. -/
theorem sourceStepXI_roundtripSpec_nonempty_iff_injective
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (N : Nat)
    (φ : ConcreteFiniteTheorem311.finiteLabel l →+ (ℤ × ℤ))
    (c₀ : SourceStepXIChoice I) :
    SourceStepXIColumnReadbackResidual I N φ c₀ ↔
      Function.Injective
        (coreColumnRealization (N := N) (sourceStepXICore I) φ c₀) := by
  unfold SourceStepXIColumnReadbackResidual
  rw [SourceRoundtripRealization.roundtripSpec_nonempty_iff]
  constructor
  · intro h
    exact coreColumnRealization_injective_of_leftInverse (sourceStepXICore I) φ c₀
      (readback_to_leftInverse (sourceStepXICore I) φ c₀ h)
  · intro h
    exact readback_of_leftInverse (sourceStepXICore I) φ c₀
      (leftInverse_of_injective (sourceStepXICore I) φ c₀ h)

/-- A roundtrip spec on the source core yields injectivity of the canonical
column realization. -/
theorem sourceStepXI_roundtripSpec_implies_injective
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (N : Nat)
    (φ : ConcreteFiniteTheorem311.finiteLabel l →+ (ℤ × ℤ))
    (c₀ : SourceStepXIChoice I) :
    SourceStepXIColumnReadbackResidual I N φ c₀ →
      Function.Injective
        (coreColumnRealization (N := N) (sourceStepXICore I) φ c₀) :=
  (sourceStepXI_roundtripSpec_nonempty_iff_injective I N φ c₀).mp

/-- Injectivity of the canonical column realization supplies the roundtrip spec
on the source core. -/
theorem sourceStepXI_injective_implies_roundtripSpec
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (N : Nat)
    (φ : ConcreteFiniteTheorem311.finiteLabel l →+ (ℤ × ℤ))
    (c₀ : SourceStepXIChoice I) :
    Function.Injective
        (coreColumnRealization (N := N) (sourceStepXICore I) φ c₀) →
      SourceStepXIColumnReadbackResidual I N φ c₀ :=
  (sourceStepXI_roundtripSpec_nonempty_iff_injective I N φ c₀).mpr

end LeanFormal.IUT.XiFPaper.S3138SourceRoundtripRealizationActual

end
