/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1RootUnitMassCitizenActual
import Mathlib.Tactic

/-! # #10: root unit-ball mass = 1 criterion -/
noncomputable section
open scoped BigOperators ENNReal
namespace LeanFormal.IUT.XiFPaper.Mzk1RootUnitMassOneCriterionActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1RootUnitMassCitizenActual
open LeanFormal.IUT.XiFPaper.Mzk1NativeNormalizedUnitMassConditionalActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem rootUnitBallMass_eq_one_iff_prod
    (hSigma : ∀ b, SigmaFinite (rootExtensionHaar T b)) :
    rootUnitBallMass (T := T) = 1 ↔ (∏ b, rootUnitMass (T := T) b) = 1 := by
  haveI := hSigma
  rw [rootUnitBallMass_eq_prod_rootUnitMass]

theorem rootUnitBallMass_eq_one_iff_normalized
    (h : rootUnitBallMass (T := T) = 1) :
    (rootUnitBallMass (T := T))⁻¹ * rootUnitBallMass (T := T) = 1 :=
  normalizedRootUnitBallMass_eq_one (T := T)

end LeanFormal.IUT.XiFPaper.Mzk1RootUnitMassOneCriterionActual
