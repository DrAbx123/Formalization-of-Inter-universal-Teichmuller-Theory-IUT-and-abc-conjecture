/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A2 node04 §7.3: tensor unit-ball exact interface -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node04TensorUnitBallInterfaceActual

/-- Exact data for the actual tensor decomposition and the integral-lattice
unit-ball statement; no arbitrary tensor norm is used. -/
structure A2Node04TensorUnitBallInterface
    (A : Type*) [CommRing A]
    (ι : Type*) (E : ι → Type*) [∀ i, CommRing (E i)] where
  decomposition : A ≃+* (∀ i, E i)
  integralLattice : Set A
  unitBall : Set (∀ i, E i)
  decomposition_maps_integral :
    Set.MapsTo decomposition integralLattice unitBall

def A2Node04TensorUnitBallInterfaceRequired
    (A : Type*) [CommRing A]
    (ι : Type*) (E : ι → Type*) [∀ i, CommRing (E i)] : Prop :=
  Nonempty (A2Node04TensorUnitBallInterface A ι E)

end LeanFormal.IUT.XiFPaper.Mzk1A2Node04TensorUnitBallInterfaceActual
