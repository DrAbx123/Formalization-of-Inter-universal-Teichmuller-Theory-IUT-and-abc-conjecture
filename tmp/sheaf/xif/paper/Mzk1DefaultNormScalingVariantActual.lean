/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import Mathlib.Tactic
/-! # Default-norm variant of pure fractional scaling data (type-level probe)

This is a **separate** structure, not a replacement for
`ArithmeticTuplePureFractionalScalingData`.  Its localGenerator lives in the
default `Completion` norm, not the normalized `CommonPrimeCompletion` instance.
The goal is to check whether a default-norm supply can be built and consumed.
No existing object semantics are changed.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1DefaultNormScalingVariantActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable (c : ι → Real)
/-- Minimal default-norm scaling supply: generator in the default completion norm. -/
structure DefaultNormPureFractionalScalingData where
  localGenerator : (i : ι) → Completion (places i (tuple i)).val
  localGenerator_norm : ∀ i,
    ‖localGenerator i‖ = (p : Real) ^ (-(c i))
/-- Constructor analogous to the normalized `_ofGenerator` at the generator/norm level. -/
def defaultNormPureFractionalScalingData_ofGenerator
    (g : (i : ι) → Completion (places i (tuple i)).val)
    (hg : ∀ i, ‖g i‖ = (p : Real) ^ (-(c i))) :
    DefaultNormPureFractionalScalingData places tuple c where
  localGenerator := g
  localGenerator_norm := hg
/-- The default-norm structure is not the normalized one: its generator type is
`Completion place`, while `ArithmeticTuplePureFractionalScalingData.localGenerator`
is `CommonPrimeCompletion place`.  A consumer expecting the latter needs a bridge. -/
def DefaultNormScalingConsumerGap : Prop :=
  Nonempty (DefaultNormPureFractionalScalingData places tuple c)
end LeanFormal.IUT.XiFPaper.Mzk1DefaultNormScalingVariantActual
end
