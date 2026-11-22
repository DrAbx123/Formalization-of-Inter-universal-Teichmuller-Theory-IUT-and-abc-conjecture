/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import Mathlib.Tactic

/-! # #10: correct root-extension carrier (not base-completion tensor) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaRootCarrierActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The correct product carrier: product of root extensions over the bad places. -/
abbrev ThetaRootCarrier : Type := RootExtensionProductCarrier T

theorem thetaRootCarrier_eq_s1902Carrier :
    ThetaRootCarrier T = S1902Carrier T := rfl

/-- Carrier-level identity equivalence on the correct root-extension product. -/
def thetaRootCarrierEquiv : ThetaRootCarrier T ≃ S1902Carrier T :=
  Equiv.refl _

theorem thetaRootCarrierEquiv_apply (x : ThetaRootCarrier T) :
    thetaRootCarrierEquiv T x = x := rfl

def rows : List (String × String) :=
  [ ("ThetaRootCarrier", "root-extension product, not base completion tensor"),
    ("thetaRootCarrier_eq_s1902Carrier", "new proof: rfl"),
    ("thetaRootCarrierEquiv", "new construction: refl equivalence") ]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1ThetaRootCarrierActual
