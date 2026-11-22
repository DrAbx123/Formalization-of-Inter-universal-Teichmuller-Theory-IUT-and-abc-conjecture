/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3S1902UnitMassCitizenActual
import Mathlib.Tactic

/-! # #10: native unitMass = 1 exact condition -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1NativeUnitMassOneActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902UnitMassCitizenActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
def NativeUnitMassOneCondition : Prop := actualUnitMass (T := T) = 1
theorem nativeUnitMassOne_iff :
    NativeUnitMassOneCondition (T := T) ↔ actualUnitMass (T := T) = 1 := Iff.rfl
def nativeUnitMassOneRows : List (String × String) :=
  [ ("NativeUnitMassOneCondition", "actualUnitMass = 1, exact condition"),
    ("actualUnitMass", "(s1915UnitMass T).toReal; computed value"),
    ("unitMass=1", "GAP: needs normalized vs unnormalized rootExtensionHaar comparison") ]
theorem nativeUnitMassOneRows_length : nativeUnitMassOneRows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NativeUnitMassOneActual
