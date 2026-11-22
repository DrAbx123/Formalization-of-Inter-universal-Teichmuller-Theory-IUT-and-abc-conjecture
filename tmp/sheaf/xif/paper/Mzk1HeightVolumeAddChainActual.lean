import Mathlib

/-!
# Mzk1HeightVolumeAddChainActual — chained height/volume addition consumers (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumers: componentwise height≤volume implies sum height≤sum volume. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HeightVolumeAddChainActual

/-- Chained: componentwise comparison passes to two-term sums. -/
theorem height_volume_add_chain {h1 h2 v1 v2 : ℚ}
    (H1 : h1 ≤ v1) (H2 : h2 ≤ v2) : h1 + h2 ≤ v1 + v2 :=
  add_le_add H1 H2

/-- Chained: componentwise comparison passes to three-term sums. -/
theorem height_volume_add_chain3 {h1 h2 h3 v1 v2 v3 : ℚ}
    (H1 : h1 ≤ v1) (H2 : h2 ≤ v2) (H3 : h3 ≤ v3) :
    h1 + h2 + h3 ≤ v1 + v2 + v3 :=
  add_le_add (add_le_add H1 H2) H3

/-- Chained: nonnegative heights with componentwise bounds give nonnegative volume sum. -/
theorem height_volume_nonneg_chain {h1 h2 v1 v2 : ℚ}
    (H1 : h1 ≤ v1) (H2 : h2 ≤ v2) (h1n : 0 ≤ h1) (h2n : 0 ≤ h2) :
    0 ≤ v1 + v2 :=
  add_nonneg (le_trans h1n H1) (le_trans h2n H2)

end LeanFormal.IUT.XiFPaper.Mzk1HeightVolumeAddChainActual
