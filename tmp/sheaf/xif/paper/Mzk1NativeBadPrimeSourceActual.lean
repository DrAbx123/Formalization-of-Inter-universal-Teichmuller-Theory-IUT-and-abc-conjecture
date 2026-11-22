/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NativeBadPrimeActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativeCommonPrime
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import Mathlib.Tactic

/-! # #10: NativeBadPrimeData reduces to fixed prime on Bad moduli places -/
noncomputable section
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1NativeBadPrimeActual
namespace LeanFormal.IUT.XiFPaper.Mzk1NativeBadPrimeSourceActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The rational prime of the native bad K-place equals the rational prime of
the underlying Bad moduli place. -/
theorem nativeBadToKPlace_completionRationalPrime
    (b : Bad (nativePlaceSelection T)) :
    completionRationalPrime (nativeBadToKPlace T b) = completionRationalPrime b.1 := by
  rw [← completionRationalPrime_comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b),
    nativeBadToKPlace_comap T b]

/-- Exact source condition: all Bad moduli places have fixed rational prime p. -/
def NativeBadModuliFixedPrime (p : ℕ) : Prop :=
  ∀ b : Bad (nativePlaceSelection T), (completionRationalPrime b.1).val = p

/-- `NativeBadModuliFixedPrime` implies the `NativeBadPrimeData` needed for
CommonPrimeCompletion. -/
theorem nativeBadPrimeData_of_moduliFixed {p : ℕ}
    (h : NativeBadModuliFixedPrime (T := T) p) :
    NativeBadPrimeData (T := T) p := by
  intro b
  rw [nativeBadToKPlace_completionRationalPrime T b]
  exact h b

def nativeBadPrimeSourceRows : List (String × String) :=
  [ ("nativeBadToKPlace_completionRationalPrime", "green: prime = prime of underlying Bad place"),
    ("NativeBadModuliFixedPrime", "exact source condition: all Bad places have prime p"),
    ("nativeBadPrimeData_of_moduliFixed", "green: moduli fixed prime => NativeBadPrimeData"),
    ("source of fixed prime", "GAP: Bad only has odd residue characteristic, no fixed p") ]
theorem nativeBadPrimeSourceRows_length : nativeBadPrimeSourceRows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NativeBadPrimeSourceActual
