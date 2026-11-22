/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DetLinePrincipalGeneratorActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1 native count <-> local valuation interface -/
noncomputable section
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
namespace LeanFormal.IUT.XiFPaper.Mzk1P1CountLocalValuationNativeActual
variable {k : Type} [Field k] [NumberField k]
/-- Named native bridge: count exponent, generator, and local valuation agree. -/
structure NativeCountLocalValuationData (I : LineBundle (k := k))
    (v : NumberField.FinitePlace k) where
  e : Int
  generator : LocalField (k := k) v
  count_eq : countExponent (k := k) v I = e
  valuation_eq : (Valued.v (generator : LocalField (k := k) v)).log = -e
  span_eq : localizedLine (k := k) I v =
    Submodule.span (LocalRing (k := k) v) {generator}
def NativeCountLocalValuationDataRequired
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k) : Prop :=
  Nonempty (NativeCountLocalValuationData I v)
def countValuationRows : List (String × String) :=
  [ ("NativeCountLocalValuationData", "count e + generator + valuation=-e + span"),
    ("CountLocalizationBridge", "mainline span input; this file is native data side"),
    ("inhabitant", "GAP: bridge not constructed") ]
theorem countValuationRows_length : countValuationRows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P1CountLocalValuationNativeActual
