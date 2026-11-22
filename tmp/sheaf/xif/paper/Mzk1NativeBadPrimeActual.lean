/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1BadPlaceUnitMassProductActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import Mathlib.Tactic

/-! # #10: nativeBad prime interface -> CommonPrimeCompletion product -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1NativeBadPrimeActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1LocalUnitMassProductActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Exact named input: every `nativeBadToKPlace T b` has rational prime `p`. -/
def NativeBadPrimeData (p : ℕ) : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    (completionRationalPrime (nativeBadToKPlace T b)).val = p

/-- Under `NativeBadPrimeData`, the native bad K-place is a `FinitePlaceAtPrime`. -/
noncomputable def nativeBadToKPlaceAtPrime {p : ℕ} (h : NativeBadPrimeData (T := T) p)
    (b : Bad (nativePlaceSelection T)) :
    FinitePlaceAtPrime T.arithmetic.K p :=
  ⟨nativeBadToKPlace T b, h b⟩

/-- The actual T-specific product on `CommonPrimeCompletion` carriers, under the
single named prime-interface. -/
theorem badPlaceCommonPrimeUnitMassProduct_eq_one {p : ℕ}
    (h : NativeBadPrimeData (T := T) p)
    [∀ b, MeasurableSpace (CommonPrimeCompletion (nativeBadToKPlaceAtPrime (T := T) h b))]
    [∀ b, BorelSpace (CommonPrimeCompletion (nativeBadToKPlaceAtPrime (T := T) h b))] :
    localUnitMassProduct
        (K := fun b => CommonPrimeCompletion (nativeBadToKPlaceAtPrime (T := T) h b)) = 1 :=
  localUnitMassProduct_eq_one

def nativeBadPrimeRows : List (String × String) :=
  [ ("NativeBadPrimeData", "single named input: completionRationalPrime(nativeBadToKPlace T b)=p"),
    ("nativeBadToKPlaceAtPrime", "constructs FinitePlaceAtPrime from data"),
    ("badPlaceCommonPrimeUnitMassProduct_eq_one", "product=1 on CommonPrimeCompletion, conditional"),
    ("source of NativeBadPrimeData", "GAP: no prime-equality field in Bad/native selection"),
    ("blockEquiv/unitMass citizen", "GAP") ]
theorem nativeBadPrimeRows_length : nativeBadPrimeRows.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NativeBadPrimeActual
