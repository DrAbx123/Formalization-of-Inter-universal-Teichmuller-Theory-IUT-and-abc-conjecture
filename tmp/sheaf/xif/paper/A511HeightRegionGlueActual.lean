/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.A503HeightRegionObjectActual

/-! # A511 glue: height/event-weight bundle extending the A503 object layer -/

noncomputable section

namespace LeanFormal.IUT.Objects.HeightRegion

open LeanFormal.IUT

/-- Glue object: the height/region-weight data of an ABC triple together with the
rational point's weight and the height data from `HeightRegionObject`. -/
structure HeightRegionBundle where
  /-- The A503 height-region object. -/
  data : HeightRegionObject
  /-- The rational point attached to the triple. -/
  point : { x : ℚ // True }
  /-- The paper arithmetic weight of the triple. -/
  weight : ℝ
  weight_eq : weight = data.weightData.weight
  /-- The paper log-height of the triple. -/
  height : ℝ
  height_eq : height = data.height

/-- Build the bundle from concrete height-region data (all fields from existing objects). -/
def heightRegionBundleOf (D : HeightRegionObject) (x : ℚ) : HeightRegionBundle where
  data := D
  point := ⟨x, trivial⟩
  weight := D.weightData.weight
  weight_eq := rfl
  height := D.height
  height_eq := rfl

/-- The bundled weight is the arithmetic weight of the underlying triple. -/
theorem heightRegionBundle_weight_eq (a b c : Nat) (h : IsABCTriple a b c) :
    (heightRegionBundleOf (heightRegionOf a b c h) (0 : ℚ)).weight =
      arithmeticWeight (abcRationalPoint a c) := rfl

/-- The bundled height is the log-height of the underlying rational point. -/
theorem heightRegionBundle_height_eq (a b c : Nat) (h : IsABCTriple a b c) :
    (heightRegionBundleOf (heightRegionOf a b c h) (0 : ℚ)).height =
      Height.logHeight₁ (abcRationalPoint a c) := rfl

/-- Nonnegativity of the bundled weight (glue of `arithmeticWeight_nonneg`). -/
theorem heightRegionBundle_weight_nonneg (a b c : Nat) (h : IsABCTriple a b c) :
    0 ≤ (heightRegionBundleOf (heightRegionOf a b c h) (0 : ℚ)).weight :=
  arithmeticWeight_nonneg _

end LeanFormal.IUT.Objects.HeightRegion
