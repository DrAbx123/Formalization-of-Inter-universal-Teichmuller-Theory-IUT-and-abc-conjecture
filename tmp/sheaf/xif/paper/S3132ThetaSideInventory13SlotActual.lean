set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Paper-route Theta side: 13-slot inventory

Machine-checkable inventory of the 13 slots of the Theta-side comparison-region
bundle, with the concrete provider/status of each slot.  Data record only.
Pins: registry 13129 frozen.
-/

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideInventory13SlotActual

/-- One inventory slot. -/
structure InventorySlot where
  index : Nat
  name : String
  provider : String
  status : String

/-- The 13 slots of the Theta-side bundle. -/
def thetaSideInventory : List InventorySlot :=
  [ { index := 1, name := "arithmetic",
      provider := "concreteGaussianInitialThetaArithmeticData l",
      status := "concrete existing" }
  , { index := 2, name := "minimal-clause-data",
      provider := "LGPModelSourceClauseMissing l (signQuotient + assembly A-F)",
      status := "exact DATA residual (stage4); construction from witness via LGPConcreteClauseData" }
  , { index := 3, name := "native-theta-datum",
      provider := "lgpModelNativeData / lgpConcreteClauseData_toNativeData",
      status := "constructive from slot 2" }
  , { index := 4, name := "haar-family",
      provider := "lgpNativeHaarFamily T (additive Haar)",
      status := "concrete existing (stage4); normalization free" }
  , { index := 5, name := "normalization-factor",
      provider := "sourceThetaNormalizationFactor_eq_zero",
      status := "CLOSED (unit-reference mass 1)" }
  , { index := 6, name := "rooted-scaling-data-R1",
      provider := "RootedScalingData (logExpScalar / paperFormulaScalar)",
      status := "content-free in exp form; explicit formula form under PaperRootHullFormulaGap" }
  , { index := 7, name := "weighted-rooted-identity-R2",
      provider := "WeightedRootedIdentity",
      status := "sharp remaining residual (paper log-volume dictionary; III Prop 3.9(i))" }
  , { index := 8, name := "vform-canonical-identity",
      provider := "vformCanonical_of_weightedIdentity",
      status := "follows from slots 6+7 (elementary)" }
  , { index := 9, name := "canonical-source-readout",
      provider := "thetaSideSharpResidual_canonicalReadout / weightedIdentity_canonicalReadout",
      status := "follows from slots 6+7" }
  , { index := 10, name := "comparison-payload",
      provider := "AdaptedCorollary312ComparisonData (modelComparisonData)",
      status := "constructive from slots 3+4+7+10" }
  , { index := 11, name := "q-side-signed-data",
      provider := "qSigned with 0 < -qSigned and qSigned <= -thetaSigned",
      status := "explicit hypothesis (q-side stream)" }
  , { index := 12, name := "comparison-region-bundle",
      provider := "ThetaSideComparisonRegionBundle",
      status := "constructive from slots 2-11" }
  , { index := 13, name := "iv-genell-interface",
      provider := "AdaptedIVGenEllShadow.genEll_transfer",
      status := "[GenEll] Theorem 2.1 source anchor (reduction, not proof of ABC)" } ]

/-- The inventory has 13 slots. -/
theorem thetaSideInventory_length : thetaSideInventory.length = 13 := rfl

/-- The inventory indices are 1..13. -/
theorem thetaSideInventory_indices :
    thetaSideInventory.map (fun s => s.index) =
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] := rfl

#check InventorySlot
#check thetaSideInventory
#check thetaSideInventory_length
#check thetaSideInventory_indices

end LeanFormal.IUT.XiFPaper.S3132ThetaSideInventory13SlotActual