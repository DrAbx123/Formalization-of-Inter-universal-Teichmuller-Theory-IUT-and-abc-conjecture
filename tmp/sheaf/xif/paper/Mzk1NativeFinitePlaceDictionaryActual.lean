/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NativeBadPrimeActual
import tmp.sheaf.xif.paper.Mzk1C3S1902UnitMassCitizenActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import Mathlib.Tactic

/-! # #10 finite-place dictionary on native data (no C3 inhabitant) -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1NativeFinitePlaceDictionaryActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1NativeBadPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1LocalUnitMassProductActual
open LeanFormal.IUT.XiFPaper.Mzk1C3S1902UnitMassCitizenActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Native finite-place dictionary: fixed prime data for all bad places and the
carrier measurability needed by the normalized product. -/
structure NativeFinitePlaceDictionaryData where
  p : ℕ
  [hp : Fact p.Prime]
  primeData : NativeBadPrimeData (T := T) p
  measurableSpace : ∀ b : Bad (nativePlaceSelection T),
    MeasurableSpace (CommonPrimeCompletion (nativeBadToKPlaceAtPrime (T := T) primeData b))
  borelSpace : ∀ b : Bad (nativePlaceSelection T),
    BorelSpace (CommonPrimeCompletion (nativeBadToKPlaceAtPrime (T := T) primeData b))

/-- Product of normalized local unit masses on the native carrier is `1`. -/
theorem nativeDictionary_unitMassProduct_eq_one
    (D : NativeFinitePlaceDictionaryData (T := T))
    [∀ b, MeasurableSpace (CommonPrimeCompletion (nativeBadToKPlaceAtPrime (T := T) D.primeData b))]
    [∀ b, BorelSpace (CommonPrimeCompletion (nativeBadToKPlaceAtPrime (T := T) D.primeData b))] :
    localUnitMassProduct
        (K := fun b => CommonPrimeCompletion (nativeBadToKPlaceAtPrime (T := T) D.primeData b)) = 1 :=
  badPlaceCommonPrimeUnitMassProduct_eq_one (T := T) D.primeData

/-- The actual S1915 unit mass is a T-only object (no C3 inhabitant). -/
theorem nativeDictionary_unitMass_eq_actual :
    actualUnitMass (T := T) = (s1915UnitMass T).toReal := rfl

def nativeDictionaryRows : List (String × String) :=
  [ ("NativeFinitePlaceDictionaryData", "p + NativeBadPrimeData + carrier measurability; no C3"),
    ("nativeDictionary_unitMassProduct_eq_one", "∏ normalized μ_b(O_b)=1 on native carrier"),
    ("nativeDictionary_unitMass_eq_actual", "actualUnitMass=(s1915UnitMass T).toReal"),
    ("unitMass=1", "GAP: rootExtensionHaar unnormalized") ]
theorem nativeDictionaryRows_length : nativeDictionaryRows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NativeFinitePlaceDictionaryActual
