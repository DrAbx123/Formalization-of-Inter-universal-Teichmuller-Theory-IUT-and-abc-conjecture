/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3S1902BlockEquivDataActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import Mathlib.Tactic

/-! # #10 citizen: actual C3S1902UnitMassData inhabitant -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1C3S1902UnitMassCitizenActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902BlockEquivDataActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual S1915 unit mass, as a real number. -/
noncomputable def actualUnitMass : ℝ :=
  (s1915UnitMass T).toReal

theorem actualUnitMass_pos : 0 < actualUnitMass (T := T) := by
  unfold actualUnitMass
  exact ENNReal.toReal_pos (ne_of_gt (s1915_unitMass_pos T)) (ne_of_lt (s1915_unitMass_lt_top T))

/-- Actual inhabitant of `C3S1902UnitMassData`: the unit mass is the S1915
product unit-ball mass, with its actual positivity. -/
noncomputable def actualC3S1902UnitMassData :
    C3S1902UnitMassData T where
  unitMass := actualUnitMass (T := T)
  unitMass_pos := actualUnitMass_pos (T := T)
  unitMass_eq := rfl

theorem actualC3S1902UnitMassData_nonempty :
    Nonempty (C3S1902UnitMassData T) := ⟨actualC3S1902UnitMassData T⟩

def unitMassCitizenRows : List (String × String) :=
  [ ("actualUnitMass", "(s1915UnitMass T).toReal"),
    ("actualUnitMass_pos", "green from s1915_unitMass_pos/lt_top"),
    ("actualC3S1902UnitMassData", "actual unitMass citizen inhabitant"),
    ("unitMass=1", "GAP: no normalized unit-ball mass theorem for additive rootExtensionHaar") ]
theorem unitMassCitizenRows_length : unitMassCitizenRows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C3S1902UnitMassCitizenActual
