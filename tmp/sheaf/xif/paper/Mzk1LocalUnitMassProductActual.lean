/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.AbsTopIII07NormalizedLocalVolumeActual
import Mathlib.Tactic

/-! # #10: product of normalized local unit-lattice masses -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Metric
namespace LeanFormal.IUT.XiFPaper.Mzk1LocalUnitMassProductActual
open LeanFormal.IUT.XiFPaper.AbsTopIII07NormalizedLocalVolumeActual
universe u
variable {ι : Type*} [Fintype ι]
variable {K : ι → Type*}
variable [∀ i, NormedField (K i)] [∀ i, IsUltrametricDist (K i)]
  [∀ i, ProperSpace (K i)] [∀ i, MeasurableSpace (K i)] [∀ i, BorelSpace (K i)]

/-- Product of the normalized local unit-lattice masses. -/
noncomputable def localUnitMassProduct : ℝ :=
  ∏ i, (normalizedHaar (K := K i) (unitBall (K := K i))).toReal

theorem normalizedHaar_unitBall_toReal (i : ι) :
    (normalizedHaar (K := K i) (unitBall (K := K i))).toReal = 1 := by
  rw [normalizedHaar_unitBall]
  norm_num

/-- Every normalized unit lattice has mass 1, so the product is 1. -/
theorem localUnitMassProduct_eq_one :
    localUnitMassProduct (K := K) = 1 := by
  unfold localUnitMassProduct
  simp [normalizedHaar_unitBall_toReal]

theorem localUnitMassProduct_pos : 0 < localUnitMassProduct (K := K) := by
  rw [localUnitMassProduct_eq_one]
  norm_num

def localUnitProductRows : List (String × String) :=
  [ ("localUnitMassProduct", "∏_v μ_v(O_v), normalized"),
    ("localUnitMassProduct_eq_one", "green: each μ_v(O_v)=1"),
    ("actual Bad(nativePlaceSelection T) index", "GAP: T-specific product not instantiated"),
    ("product into C3S1902 HaarScaleData", "GAP: blockEquiv/unitMass citizen") ]
theorem localUnitProductRows_length : localUnitProductRows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1LocalUnitMassProductActual
