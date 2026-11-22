/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A2 node04 §7.1: relative norm / q-contraction exact interface -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node04RelativeNormInterfaceActual

/-- Exact data for the relative-norm / q-contraction step, for local fields
`K ⊆ L`.  The norm formula is the actual spectral norm comparison; no
inhabitant is supplied. -/
structure A2Node04RelativeNormInterface
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [NormedField K] [NormedField L] where
  relativeNorm : L →* K
  norm_formula :
    ∀ x : L, ‖relativeNorm x‖ = ‖x‖ ^ Module.finrank K L
  q_contraction :
    ∀ q : K, ‖q‖ < 1 → ‖relativeNorm (algebraMap K L q)‖ < 1

def A2Node04RelativeNormInterfaceRequired
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [NormedField K] [NormedField L] : Prop :=
  Nonempty (A2Node04RelativeNormInterface K L)

end LeanFormal.IUT.XiFPaper.Mzk1A2Node04RelativeNormInterfaceActual
