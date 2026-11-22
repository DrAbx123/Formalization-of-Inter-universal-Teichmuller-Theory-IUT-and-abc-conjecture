/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-! # A503 object layer: height/region-weight objects for Gap 1/2 (IUT IV) -/

noncomputable section

namespace LeanFormal.IUT.Objects.HeightRegion

open LeanFormal.IUT

/-- The arithmetic-weight object of IUT IV at a rational point: the concrete arithmetic
weight of the rational point attached to an ABC triple. -/
structure RegionWeightObject where
  /-- The numerator. -/
  a : Nat
  /-- The lower term. -/
  b : Nat
  /-- The denominator. -/
  c : Nat
  /-- The triple is an ABC triple. -/
  triple : IsABCTriple a b c
  /-- The actual arithmetic weight `log(radical(abc))`. -/
  weight : Real
  /-- Source: the weight is the arithmetic weight of the rational point `a/c`. -/
  weight_eq : weight = arithmeticWeight (abcRationalPoint a c)

/-- The height object of IUT IV: the log-height of the rational point and the
arithmetic weight associated with it, together with the theta bound read from the
q-pilot object (real data, not a Prop shell). -/
structure HeightRegionObject where
  /-- The arithmetic-weight object of the same triple. -/
  weightData : RegionWeightObject
  /-- The actual log-height of `a/c`. -/
  height : Real
  /-- Source: the height is the paper log-height of the rational point. -/
  height_eq : height = Height.logHeight₁ (abcRationalPoint weightData.a weightData.c)

/-- The region-weight object attached to a concrete ABC triple. -/
def regionWeightOf (a b c : Nat) (h : IsABCTriple a b c) : RegionWeightObject where
  a := a
  b := b
  c := c
  triple := h
  weight := arithmeticWeight (abcRationalPoint a c)
  weight_eq := rfl

/-- The height-region object attached to a concrete ABC triple. -/
def heightRegionOf (a b c : Nat) (h : IsABCTriple a b c) : HeightRegionObject where
  weightData := regionWeightOf a b c h
  height := Height.logHeight₁ (abcRationalPoint a c)
  height_eq := rfl

/-- The region-weight object is positive: the arithmetic weight of an ABC triple is
nonnegative (real content from the dictionary layer). -/
theorem regionWeightOf_nonneg (a b c : Nat) (h : IsABCTriple a b c) :
    0 ≤ (regionWeightOf a b c h).weight :=
  arithmeticWeight_nonneg _

/-- The height of the height-region object is nonnegative on ABC triples. -/
theorem heightRegionOf_height_nonneg (a b c : Nat) (h : IsABCTriple a b c) :
    0 ≤ (heightRegionOf a b c h).height := by
  have hheight : (heightRegionOf a b c h).height = Real.log (c : ℝ) := by
    rw [show (heightRegionOf a b c h).height = Height.logHeight₁ (abcRationalPoint a c) from rfl]
    exact abcRationalPoint_logHeight₁ h
  rw [hheight]
  exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt h.c_pos))

end LeanFormal.IUT.Objects.HeightRegion
