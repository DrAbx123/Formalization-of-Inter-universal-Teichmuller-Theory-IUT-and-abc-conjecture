/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NativeBadPrimeSourceActual
import Mathlib.Tactic

/-! # #10: NativeBadPrimeData iff NativeBadModuliFixedPrime -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1NativeBadPrimeIffActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1NativeBadPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1NativeBadPrimeSourceActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem nativeBadPrimeData_iff_moduliFixed {p : ℕ} :
    NativeBadPrimeData (T := T) p ↔ NativeBadModuliFixedPrime (T := T) p := by
  constructor
  · intro h b
    have hb := h b
    rwa [nativeBadToKPlace_completionRationalPrime T b] at hb
  · exact nativeBadPrimeData_of_moduliFixed (T := T)

def rows : List (String × String) :=
  [ ("nativeBadPrimeData_iff_moduliFixed", "new proof: source reduction is an iff") ]
theorem rows_length : rows.length = 1 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NativeBadPrimeIffActual
