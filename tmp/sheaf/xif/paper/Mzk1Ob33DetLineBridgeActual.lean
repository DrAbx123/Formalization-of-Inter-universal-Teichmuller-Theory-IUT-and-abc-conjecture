/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DetLineConstructionActual
import tmp.sheaf.xif.paper.Mzk1Ob33DetLineFromBadPrimeSourceActual
import tmp.sheaf.xif.paper.Mzk1Ob33DetLineActual
import Mathlib.Tactic

/-! # Route B #3 step 5: Ob33 actual det-line degree = relative determinant log + reference

Bridges the actual q-pilot arithmetic degree from `Mzk1Ob33DetLineFromBadPrimeSourceActual`
with the relative determinant construction of `Mzk1DetLineConstructionActual`
(`globalLogVolume_relativeDetLine : log D(H,O) = log H - log O`).

Consequence: the semantic identification `RouteBArithmeticDegreeReadingGap`
(qPilotDetArithmeticDegree = routeBThetaNormalized) is *equivalent* to the
relative-determinant form `log D(H,O) + log O = routeBThetaNormalized C3`.
The reference line bundle `O` and the nonzero witnesses are explicit inputs.
-/

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineFromBadPrimeSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLineConstructionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual bad-prime q-pilot arithmetic degree is the global log-volume of the
q-pilot line bundle (rfl-level re-export). -/
theorem qPilotDetArithmeticDegreeOfBadPrimes_eq_globalLogVolume :
    qPilotDetArithmeticDegreeOfBadPrimes T =
      globalLogVolume (k := T.arithmetic.K)
        (badPrimeSource T).qPilotLineBundle := by
  rw [qPilotDetArithmeticDegreeOfBadPrimes, qPilotDetArithmeticDegree_eq_globalLogVolume]

/-- **Step 5 bridge**: the arithmetic degree is the relative determinant log-volume of
the q-pilot line bundle against any reference line bundle, plus that reference log.
This is `globalLogVolume_relativeDetLine` applied to the actual source. -/
theorem qPilotDetArithmeticDegreeOfBadPrimes_eq_relativeDetLog_add
    (O : LineBundle (k := T.arithmetic.K))
    (hH : (badPrimeSource T).qPilotLineBundle ≠ 0) (hO : O ≠ 0) :
    qPilotDetArithmeticDegreeOfBadPrimes T =
      relativeDetLog (k := T.arithmetic.K)
        (badPrimeSource T).qPilotLineBundle O +
        globalLogVolume (k := T.arithmetic.K) O := by
  rw [qPilotDetArithmeticDegreeOfBadPrimes_eq_globalLogVolume]
  have h := globalLogVolume_relativeDetLine (k := T.arithmetic.K)
    ((badPrimeSource T).qPilotLineBundle) O hH hO
  unfold relativeDetLog
  linarith

/-- The Route B gap in relative-determinant form. -/
theorem routeB_gap_iff_relativeDetLog_form
    {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (O : LineBundle (k := T.arithmetic.K))
    (hH : (badPrimeSource T).qPilotLineBundle ≠ 0) (hO : O ≠ 0) :
    RouteBArithmeticDegreeReadingGap T.arithmetic (badPrimeSource T) C3 ↔
      relativeDetLog (k := T.arithmetic.K)
          (badPrimeSource T).qPilotLineBundle O +
        globalLogVolume (k := T.arithmetic.K) O =
        routeBThetaNormalized C3 := by
  unfold RouteBArithmeticDegreeReadingGap
  change qPilotDetArithmeticDegreeOfBadPrimes T = routeBThetaNormalized C3 ↔
      relativeDetLog (k := T.arithmetic.K) (badPrimeSource T).qPilotLineBundle O +
        globalLogVolume (k := T.arithmetic.K) O = routeBThetaNormalized C3
  rw [qPilotDetArithmeticDegreeOfBadPrimes_eq_relativeDetLog_add T O hH hO]

/-- The semantic identification of the actual source is equivalent to the
relative-determinant form (same content, now in B4/B5 language). -/
theorem badPrimeSourceReadingIdentification_iff_relativeDetLog
    {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (O : LineBundle (k := T.arithmetic.K))
    (hH : (badPrimeSource T).qPilotLineBundle ≠ 0) (hO : O ≠ 0) :
    BadPrimeSourceReadingIdentification T C3 ↔
      relativeDetLog (k := T.arithmetic.K)
          (badPrimeSource T).qPilotLineBundle O +
        globalLogVolume (k := T.arithmetic.K) O =
        routeBThetaNormalized C3 := by
  unfold BadPrimeSourceReadingIdentification
  change qPilotDetArithmeticDegreeOfBadPrimes T = routeBThetaNormalized C3 ↔
      relativeDetLog (k := T.arithmetic.K) (badPrimeSource T).qPilotLineBundle O +
        globalLogVolume (k := T.arithmetic.K) O = routeBThetaNormalized C3
  rw [qPilotDetArithmeticDegreeOfBadPrimes_eq_relativeDetLog_add T O hH hO]

def ob33BridgeRows : List (String × String × String) :=
  [ ("qPilotDetArithmeticDegreeOfBadPrimes_eq_globalLogVolume", "actual Ob33 degree = globalLogVolume qPilotLineBundle", "PROVED (rfl/re-export)"),
    ("qPilotDetArithmeticDegreeOfBadPrimes_eq_relativeDetLog_add", "degree = relativeDetLog(H,O) + log O", "PROVED (B4/B5)"),
    ("routeB_gap_iff_relativeDetLog_form", "RouteB gap in relative-determinant form", "PROVED (conditional on O, hH, hO)"),
    ("badPrimeSourceReadingIdentification_iff_relativeDetLog", "semantic identification iff B4/B5 form", "PROVED (conditional)"),
    ("O / hH / hO", "reference line bundle and nonzero witnesses", "input (content)") ]

theorem ob33BridgeRows_length : ob33BridgeRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineBridgeActual

end