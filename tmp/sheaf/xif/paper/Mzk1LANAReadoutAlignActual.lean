/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.lana.iut.Iut.Wall.QPilotRegion
import tmp.sheaf.lana.iut.Iut.Wall.Pilots
import tmp.sheaf.lana.iut.Iut.Wall.Rss
import tmp.sheaf.lana.iut.Iut.Wall.Checks

/-!
# Mzk1LANAReadoutAlignActual — explicit q/Theta readouts vs LANA qPilot.lhs/rhs

A494: the literal q/Theta signed readouts rewritten with the LANA quantities
`D.qPilot.absLogQ`, `D.qPilot.logQ`, `D.qPilot.lhs`, `(concreteVariantData D).rhsData.rhs`,
including the `2ℓ` normalization; the differences to the LANA q-pilot lhs/rhs are
computed, and the scaling equalities with `qScale`/`shift` proved.

* `hullReadoutLANA D = -absLogQ = lhs` (difference zero);
* `detReadoutLANA D = -absLogQ/(2ℓ) = lhs/(2ℓ)` (the 2ℓ normalization);
* `(2ℓ) * detReadoutLANA = hullReadoutLANA`;
* `hullReadoutLANA = shift D (qScale D)` (the qScale shift is the hull readout);
* `rhs - detReadoutLANA = rhs + absLogQ/(2ℓ)` (the difference to the LANA rhs).

Single file; no LANA source modified; no incomplete proof. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LANAReadoutAlignActual

open NumberField MeasureTheory
open scoped Pointwise
open Iut
open Iut.Wall

universe u
variable (D : InitialThetaData.{u})

/-- The explicit q-pilot hull readout in LANA normalization: `-|log q|`. -/
def hullReadoutLANA : Real := -D.qPilot.absLogQ

/-- The explicit Theta-pilot det readout with the `2ℓ` normalization: `-|log q|/(2ℓ)`. -/
def detReadoutLANA : Real := -D.qPilot.absLogQ / (2 * (D.ℓ : Real))

/-- The hull readout is exactly the LANA q-pilot lhs (difference zero). -/
theorem hullReadoutLANA_eq_lhs :
    hullReadoutLANA D = (concreteVariantData D).qPilot.lhs := by
  have hq : (concreteVariantData D).qPilot = D.qPilot := rfl
  rw [hq]
  rfl

/-- The det readout is the lhs divided by `2ℓ`. -/
theorem detReadoutLANA_eq_lhs_div :
    detReadoutLANA D = (concreteVariantData D).qPilot.lhs / (2 * (D.ℓ : Real)) := by
  rw [show (concreteVariantData D).qPilot.lhs = -D.qPilot.absLogQ from rfl]
  rfl

/-- The `2ℓ` normalization: `2ℓ * detReadout = hullReadout`. -/
theorem twoL_mul_detReadoutLANA :
    (2 * (D.ℓ : Real)) * detReadoutLANA D = hullReadoutLANA D := by
  unfold detReadoutLANA hullReadoutLANA
  have h5 : (5 : Nat) <= D.ℓ := D.prime.five_le
  have hℓ : (0 : Real) < (D.ℓ : Real) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) h5)
  field_simp

/-- The hull readout is the qScale shift. -/
theorem hullReadoutLANA_eq_shift_qScale :
    hullReadoutLANA D = shift D (qScale D) := by
  rw [shift_qScale]
  rfl

/-- The det readout is `-qPilotScale/(2ℓ)`, i.e. the `2ℓ`-normalized q-pilot lhs. -/
theorem detReadoutLANA_eq_neg_scale_div :
    detReadoutLANA D = -D.qPilot.absLogQ / (2 * (D.ℓ : Real)) := rfl

/-- Difference 1: the hull readout and the LANA q-pilot lhs coincide. -/
theorem hullReadoutLANA_sub_lhs :
    hullReadoutLANA D - (concreteVariantData D).qPilot.lhs = 0 := by
  rw [hullReadoutLANA_eq_lhs]
  ring

/-- Difference 2: the det readout differs from the LANA rhs by the theta-pilot hull
correction; written as the explicit formula `rhs - detReadout = rhs + absLogQ/(2ℓ)`. -/
theorem rhs_sub_detReadoutLANA :
    (concreteVariantData D).rhsData.rhs - detReadoutLANA D =
      (concreteVariantData D).rhsData.rhs + D.qPilot.absLogQ / (2 * (D.ℓ : Real)) := by
  unfold detReadoutLANA
  ring

#check hullReadoutLANA_eq_lhs
#check twoL_mul_detReadoutLANA
#check hullReadoutLANA_eq_shift_qScale
#check rhs_sub_detReadoutLANA

end LeanFormal.IUT.XiFPaper.Mzk1LANAReadoutAlignActual
end
