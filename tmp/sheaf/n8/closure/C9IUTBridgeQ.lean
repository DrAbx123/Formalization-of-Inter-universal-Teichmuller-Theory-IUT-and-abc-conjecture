import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotGlobalNormalization
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceQSideComparison

/-!
# C9 q-log bridge: actual arithmetic q log to source q-side signed value

This file is a bridge, not a proof of C1/Cor3.12.

It uses only actual project declarations:

* ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
  is the actual signed q-logarithm obtained from a finite family of
  FinitePlaceQCandidate data and the absolute-degree normalization.
* SourceQSideComparison.sourceQSideNormalizedValue is the actual signed
  normalized theta-side value at a ThetaPilotCarrier/SignedLabel.

The structure SignedQLogBridge below packages the actual q-log data and the
named comparison hypothesis

  qLog <= sourceQSideNormalizedValue

It does not introduce an arbitrary qLog : Real field, a qPilotOutput
membership, or an axiom.  The paper-faithful signed q carrier is still the
gap: the source comparison above is assumed in the bridge, not derived from
the q-pilot object, and it is not the paper target Q_can <= h_can.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.N8Closure.C9IUTBridgeQ

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotGlobalNormalization
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

/-- The actual signed q-logarithm at a selected family of rational finite
places, normalized by the absolute field degree.

The selected lower places and q-candidates are the actual data; the
absolute-degree normalization uses the lower field degree. -/
noncomputable def qLog
    (selectedLowerPlaces : Finset (NumberField.FinitePlace ℚ))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) : ℝ :=
  ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
    (k := ℚ) selectedLowerPlaces parameters

/-- The actual q-log is the negative of the corresponding actual normalized
magnitude.  This is a source identity, not a definition of a new q carrier. -/
theorem qLog_eq_neg_magnitude
    (selectedLowerPlaces : Finset (NumberField.FinitePlace ℚ))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) :
    qLog selectedLowerPlaces parameters =
      -ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerMagnitude
        (k := ℚ) selectedLowerPlaces parameters := by
  dsimp [qLog]
  exact ArithmeticQPilotGlobalNormalization.normalizedLowerSignedLog_eq_neg_magnitude
    (k := ℚ) selectedLowerPlaces parameters

/-- The actual q-log is strictly negative on a nonempty selected family. -/
theorem qLog_neg
    (selectedLowerPlaces : Finset (NumberField.FinitePlace ℚ))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty) :
    qLog selectedLowerPlaces parameters < 0 := by
  dsimp [qLog]
  exact ArithmeticQPilotGlobalNormalization.normalizedLowerSignedLog_neg
    (k := ℚ) selectedLowerPlaces parameters selected_nonempty

/-- The absolute value of the actual q-log is its actual normalized magnitude. -/
theorem abs_qLog
    (selectedLowerPlaces : Finset (NumberField.FinitePlace ℚ))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty) :
    |qLog selectedLowerPlaces parameters| =
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerMagnitude
        (k := ℚ) selectedLowerPlaces parameters := by
  rw [qLog_eq_neg_magnitude, abs_neg]
  exact abs_of_pos
    (ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerMagnitude_pos
      (k := ℚ) selectedLowerPlaces parameters selected_nonempty)

/-- The actual signed theta-side value from SourceQSideComparison. -/
noncomputable def sourceQSide
    {l : PrimeGeFive} {V : Type uv}
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) : ℝ :=
  I.sourceQSideNormalizedValue n j

/-- A bridge package with only actual q-side data.  The field q_le_source
is the named signed comparison, not an arbitrary qLog. -/
structure SignedQLogBridge
    {l : PrimeGeFive} {V : Type uv}
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  selectedLowerPlaces : Finset (NumberField.FinitePlace ℚ)
  selected_nonempty : selectedLowerPlaces.Nonempty
  parameters : (lowerPlace : selectedLowerPlaces) →
    FinitePlaceQCandidate lowerPlace.val
  n : ThetaPilotCarrier l
  j : SignedLabel l.value
  q_le_source :
    qLog selectedLowerPlaces parameters ≤ sourceQSide I n j

namespace SignedQLogBridge

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The bridge carries the actual q-log value, not a separate arbitrary real. -/
theorem qLog_eq (B : SignedQLogBridge I) :
    qLog B.selectedLowerPlaces B.parameters =
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        (k := ℚ) B.selectedLowerPlaces B.parameters := by
  rfl

theorem qLog_neg (B : SignedQLogBridge I) :
    qLog B.selectedLowerPlaces B.parameters < 0 :=
  C9IUTBridgeQ.qLog_neg B.selectedLowerPlaces B.parameters B.selected_nonempty

theorem qLog_le_source (B : SignedQLogBridge I) :
    qLog B.selectedLowerPlaces B.parameters ≤ sourceQSide I B.n B.j :=
  B.q_le_source

/-- The source q-side comparison transfers the actual q-log into the actual
signed theta-side readout.  This is the bridge content; the comparison itself
remains the named hypothesis q_le_source. -/
theorem qLog_le_sourceQSideNormalizedValue (B : SignedQLogBridge I) :
    qLog B.selectedLowerPlaces B.parameters ≤
      I.sourceQSideNormalizedValue B.n B.j :=
  B.q_le_source

end SignedQLogBridge

end LeanFormal.IUT.N8Closure.C9IUTBridgeQ

#print axioms LeanFormal.IUT.N8Closure.C9IUTBridgeQ.qLog_eq_neg_magnitude
#print axioms LeanFormal.IUT.N8Closure.C9IUTBridgeQ.qLog_neg
#print axioms LeanFormal.IUT.N8Closure.C9IUTBridgeQ.SignedQLogBridge.qLog_le_sourceQSideNormalizedValue

end
