/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # B5 ② status row table -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Ob33B5RowsFinalActual

def b5FinalRows : List (String × String × String) :=
  [ ("Mzk1Ob33B5IndexActual", "rank-one SNF / relativePlaceIndex / qpilot source", "GREEN"),
    ("Mzk1Ob33B5CountBridgeActual", "index = -count diff / num-den / placeLogVolume bridge", "GREEN (conditional on CountValuationBridge)"),
    ("Mzk1Ob33ArchMetricActual", "actual Hermitian metric + arch compatibility", "GREEN"),
    ("Mzk1Ob33B5AssemblyActual", "conditional finite+arch assembly", "GREEN (hproduct explicit)"),
    ("Mzk1P1LocalizedIsPrincipalActual", "localizedLine IsPrincipal construction/missing", "PARTIAL (exact missing instance)"),
    ("Mzk1P1LocalGeneratorFromIsPrincipalActual", "IsPrincipal => LocalGeneratorData", "GREEN conditional on instance"),
    ("Mzk1P1GeneratorNonzeroActual", "generator nonzero / hH-hO linkage", "GREEN conditional on instance"),
    ("Mzk1P1PlaceVolumeSignActual", "placeLogVolume sign from residueNormBase", "GREEN"),
    ("Mzk1B5AssemblyNoHproductAttemptActual", "named product-formula bridge / exact GAP", "GREEN conditional"),
    ("NormZpowBridge / LocalNormGeneratorBridge", "mainline norm bridge", "GREEN (generator != 0)"),
    ("CountValuationBridge / SpanGeneratorValuationLemma", "valuation = -count", "EXACT GAP"),
    ("residue-one (GAP-PC-RESDEG/tame)", "log residueNormBase = log residueCharacteristic", "ARITHMETIC INPUT") ]

theorem b5FinalRows_length : b5FinalRows.length = 12 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Ob33B5RowsFinalActual
