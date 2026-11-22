/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1UnitMassDetHaarConsumerActual
import tmp.sheaf.xif.paper.Mzk1RootUnitMassCitizenActual
import Mathlib.Tactic

/-! # #10: det-Haar consumer chain for unitMass=1 -/
noncomputable section
open scoped BigOperators ENNReal
namespace LeanFormal.IUT.XiFPaper.Mzk1UnitMassDetHaarChainActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1UnitMassDetHaarConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1RootUnitMassCitizenActual
open LeanFormal.IUT.XiFPaper.Mzk1NativeNormalizedUnitMassConditionalActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem unitMassDetHaarFactor_c_eq_rootUnitBallMass
    [∀ b, SigmaFinite (rootExtensionHaar T b)] :
    (unitMassDetHaarFactor T).c = rootUnitBallMass (T := T) := by
  rw [unitMassDetHaarFactor_c, rootUnitBallMass_eq_prod_rootUnitMass]

theorem unitMassDetHaarFactor_normalized_eq_one
    [∀ b, SigmaFinite (rootExtensionHaar T b)] :
    ((unitMassDetHaarFactor T).c)⁻¹ * rootUnitBallMass (T := T) = 1 := by
  rw [unitMassDetHaarFactor_c_eq_rootUnitBallMass]
  exact ENNReal.inv_mul_cancel (rootUnitBallMass_ne_zero (T := T))
    (rootUnitBallMass_ne_top (T := T))

end LeanFormal.IUT.XiFPaper.Mzk1UnitMassDetHaarChainActual
