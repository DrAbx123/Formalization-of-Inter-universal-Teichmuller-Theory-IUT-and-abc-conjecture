/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DiagonalIndexActual

/-! # Diagonal product scaling: cardinal re-export (task-109) -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1DiagonalProductScalingConditionActual
open LeanFormal.IUT.XiFPaper.Mzk1DiagonalIndexActual
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
theorem diagonal_quotient_cardinal (e : d → Nat) :
    Nat.card ((d → PadicInt p) ⧸ diagLatticeSubmodule (p := p) e) = ∏ i, p ^ (e i) :=
  natCard_quotient_diagLatticeSubmodule (p := p) e
def scalingRows : List (String × String) :=
  [ ("diagonal_quotient_cardinal", "green re-export"),
    ("DiagonalProductScalingCondition", "GAP: measure side") ]
theorem scalingRows_length : scalingRows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1DiagonalProductScalingConditionActual
