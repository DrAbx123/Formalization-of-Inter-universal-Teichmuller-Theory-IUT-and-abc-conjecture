/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2UnitOperationActual

open LeanFormal.IUT.LocalFieldIntegralUnits

/-- Actual units of the local integer ring have norm one: the unit operation
preserves the integral structure. -/
theorem p2UnitOperation_norm_one
    {K : Type*} [NormedField K] [IsUltrametricDist K]
    (u : (Integers K)ˣ) : ‖(u.val : K)‖ = 1 :=
  norm_unit_eq_one u

end LeanFormal.IUT.XiFPaper.Mzk1P2UnitOperationActual

end
