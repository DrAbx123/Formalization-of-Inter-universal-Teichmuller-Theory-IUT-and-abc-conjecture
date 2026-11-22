/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NativeUnitMassNormalizedProofActual
import tmp.sheaf.xif.paper.Mzk1DetHaarDegreeFactorActual
import Mathlib.Tactic

/-! # #10: unitMass factor consumed as det-Haar degree factor -/
noncomputable section
open scoped BigOperators ENNReal
namespace LeanFormal.IUT.XiFPaper.Mzk1UnitMassDetHaarConsumerActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1NativeNormalizedUnitMassConditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1NativeUnitMassNormalizedProofActual
open LeanFormal.IUT.XiFPaper.Mzk1DetHaarDegreeFactorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

noncomputable def unitMassFactor : ℝ≥0∞ :=
  ∏ b, rootUnitMass (T := T) b

theorem unitMassFactor_toReal_pos : 0 < (unitMassFactor T).toReal := by
  change 0 < (∏ b, rootUnitMass (T := T) b).toReal
  exact ENNReal.toReal_pos (ne_of_gt (unitMassFactor_pos T)) (ne_of_lt (unitMassFactor_lt_top T))

/-- The unitMass factor as a det-Haar degree factor: c = ∏ c_b, detB = c.toReal. -/
noncomputable def unitMassDetHaarFactor : DetHaarDegreeFactor where
  detB := (unitMassFactor T).toReal
  c := unitMassFactor T
  c_eq := by
    change unitMassFactor T = ENNReal.ofReal |(unitMassFactor T).toReal|
    rw [abs_of_pos (unitMassFactor_toReal_pos T)]
    exact (ENNReal.ofReal_toReal (ne_of_lt (unitMassFactor_lt_top T))).symm

theorem unitMassDetHaarFactor_c : (unitMassDetHaarFactor T).c = unitMassFactor T := rfl

end LeanFormal.IUT.XiFPaper.Mzk1UnitMassDetHaarConsumerActual
