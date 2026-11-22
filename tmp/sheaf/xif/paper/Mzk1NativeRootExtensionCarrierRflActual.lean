/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import Mathlib.Tactic

/-! # #10: S1902Carrier = root-extension product carrier -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1NativeRootExtensionCarrierRflActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem s1902Carrier_eq_rootExtensionProductCarrier :
    S1902Carrier T = RootExtensionProductCarrier T := rfl

theorem rootExtensionProductUnitBall_eq_pi :
    rootExtensionProductUnitBall T =
      Set.pi Set.univ (fun b => rootExtensionUnitBall T b) := rfl

def rows : List (String × String) :=
  [ ("s1902Carrier_eq_rootExtensionProductCarrier", "new proof: rfl"),
    ("rootExtensionProductUnitBall_eq_pi", "new proof: rfl") ]
theorem rows_length : rows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NativeRootExtensionCarrierRflActual
