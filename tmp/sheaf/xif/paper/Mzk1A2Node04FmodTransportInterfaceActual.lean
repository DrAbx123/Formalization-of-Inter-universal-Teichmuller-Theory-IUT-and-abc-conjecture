/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A2 node04 §7.2: Fmod/completion compatibility transport interface -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node04FmodTransportInterfaceActual

/-- Exact transport data along a ring equivalence `e : R ≃+* S`: the
transported valuation is `v₂(x) = v₁(e⁻¹ x)`, and the curve/q/torsion/
integer-ring compatibility is recorded as data.  No inhabitant. -/
structure A2Node04FmodTransportInterface
    (R S : Type*) [Field R] [Field S] where
  e : R ≃+* S
  valuationSource : R → WithZero (Multiplicative ℤ)
  valuationTarget : S → WithZero (Multiplicative ℤ)
  valuation_transport :
    ∀ x : S, valuationTarget x = valuationSource (e.symm x)
  curve_compat : Prop
  q_compat : Prop
  torsion_compat : Prop
  integers_compat : Prop

def A2Node04FmodTransportInterfaceRequired
    (R S : Type*) [Field R] [Field S] : Prop :=
  Nonempty (A2Node04FmodTransportInterface R S)

end LeanFormal.IUT.XiFPaper.Mzk1A2Node04FmodTransportInterfaceActual
