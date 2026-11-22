/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1LocalUnitMassProductActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import Mathlib.Tactic

/-! # #10: T-specific Bad-index local unit-mass product (index instantiation) -/
noncomputable section
open scoped BigOperators
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1LocalUnitMassProductActual
namespace LeanFormal.IUT.XiFPaper.Mzk1BadPlaceUnitMassProductActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- T-specific Bad-index product of normalized local unit masses, parameterized
by the actual per-place local fields `K b`. -/
noncomputable def badPlaceUnitMassProduct
    (K : Bad (nativePlaceSelection T) → Type u)
    [∀ b, NormedField (K b)] [∀ b, IsUltrametricDist (K b)]
    [∀ b, ProperSpace (K b)] [∀ b, MeasurableSpace (K b)] [∀ b, BorelSpace (K b)] : ℝ :=
  localUnitMassProduct (K := K)

theorem badPlaceUnitMassProduct_eq_one
    (K : Bad (nativePlaceSelection T) → Type u)
    [∀ b, NormedField (K b)] [∀ b, IsUltrametricDist (K b)]
    [∀ b, ProperSpace (K b)] [∀ b, MeasurableSpace (K b)] [∀ b, BorelSpace (K b)] :
    badPlaceUnitMassProduct (T := T) K = 1 := by
  unfold badPlaceUnitMassProduct
  exact localUnitMassProduct_eq_one (K := K)

def badPlaceUnitProductRows : List (String × String) :=
  [ ("badPlaceUnitMassProduct", "T Bad-index product, generic local fields"),
    ("badPlaceUnitMassProduct_eq_one", "green: product=1"),
    ("K b = actual Completion(nativeBadToKPlace T b)", "GAP: Completion lacks ProperSpace; CommonPrimeCompletion needs FinitePlaceAtPrime proof"),
    ("blockEquiv/unitMass citizen", "GAP") ]
theorem badPlaceUnitProductRows_length : badPlaceUnitProductRows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1BadPlaceUnitMassProductActual
