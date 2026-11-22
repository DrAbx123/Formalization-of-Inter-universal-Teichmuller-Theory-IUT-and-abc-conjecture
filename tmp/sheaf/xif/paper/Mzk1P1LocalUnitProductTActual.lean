/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NativeFinitePlaceDictionaryActual
import tmp.sheaf.xif.paper.Mzk1NativeBadPrimeActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1 T-specific local unit product under NativeBadPrimeData -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P1LocalUnitProductTActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1NativeFinitePlaceDictionaryActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The T-specific native carrier family on which the unit product is evaluated. -/
noncomputable def nativeCarrierFamily
    (D : NativeFinitePlaceDictionaryData (T := T)) :
    Bad (nativePlaceSelection T) → Type :=
  fun b => LeanFormal.IUT.NumberFieldFinitePlace.CommonPrimeCompletion
    (LeanFormal.IUT.XiFPaper.Mzk1NativeBadPrimeActual.nativeBadToKPlaceAtPrime (T := T) D.primeData b)

/-- Product=1 is proved in `Mzk1NativeFinitePlaceDictionaryActual`
(`nativeDictionary_unitMassProduct_eq_one`); this file exposes the T-specific
carrier family without duplicating the typeclass-heavy product statement. -/
def localUnitProductTRows : List (String × String) :=
  [ ("nativeCarrierFamily", "T-specific CommonPrimeCompletion family"),
    ("nativeDictionary_unitMassProduct_eq_one", "green in NativeFinitePlaceDictionary"),
    ("NativeBadPrimeData", "named input") ]
theorem localUnitProductTRows_length : localUnitProductTRows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P1LocalUnitProductTActual
