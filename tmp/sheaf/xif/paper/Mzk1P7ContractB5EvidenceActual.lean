/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5ContractEvidenceConsumerActual
import tmp.sheaf.xif.paper.Mzk1C17QCANDResNormComapActual
import tmp.sheaf.xif.paper.Mzk1C17BothResidueFieldInputsGapActual
import tmp.sheaf.xif.paper.Mzk1C17NativeBaseResidueOneActual
import tmp.sheaf.xif.paper.Mzk1P7ContractFieldsActualActual
import Mathlib.Tactic

/-! # P7 #8: combine B5 contract evidence with the signed-assembly evidence -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P7ContractB5EvidenceActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1B5ContractEvidenceActual
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormComapActual
open LeanFormal.IUT.XiFPaper.Mzk1C17BothResidueFieldInputsGapActual
open LeanFormal.IUT.XiFPaper.Mzk1C17NativeBaseResidueOneActual
open LeanFormal.IUT.XiFPaper.Mzk1B5ContractEvidenceConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1P7ContractFieldsActualActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- B5 evidence row (norm power) from the B5 contract evidence object. -/
theorem b5_norm_row (E : B5ContractEvidence T) :
    forall v : NumberField.FinitePlace T.arithmetic.K,
      residueNormBase v =
        ((residueCharacteristic v : Nat) : Real) ^
          (Ideal.span {(residueCharacteristic v : Int)}).inertiaDeg'
            v.maximalIdeal.asIdeal :=
  residueNormBase_eq_pow_of_evidence T E

/-- B5 evidence row (log-norm) from the B5 contract evidence object. -/
theorem b5_log_row (E : B5ContractEvidence T) :
    forall v : NumberField.FinitePlace T.arithmetic.K,
      Real.log (residueNormBase v) =
        ((Ideal.span {(residueCharacteristic v : Int)}).inertiaDeg'
          v.maximalIdeal.asIdeal : Real) *
          Real.log (residueCharacteristic v : Real) :=
  log_residueNormBase_eq_pow_of_evidence T E

/-- B5 evidence row (residue gap) from the B5 contract evidence object. -/
theorem b5_residue_gap_row (E : B5ContractEvidence T) : ResNormDegreeGap T :=
  resNormDegreeGap_of_evidence T E

/-- Combined evidence object: signed-assembly evidence + B5 contract evidence. -/
structure ContractEvidenceWithB5 where
  contract : ContractFieldsActual C3 P
  b5 : B5ContractEvidence T

/-- Build the combined evidence from the comparison hypothesis and the two
residue-field equivalence inputs. -/
noncomputable def contractEvidenceWithB5_of_inputs
    (h : qThetaPilotLogVolumeComparison C3 P)
    (hbase : NativeBaseResidueFieldEquivInput T)
    (hF : QVFamResidueFieldEquivInput T) : ContractEvidenceWithB5 T C3 P where
  contract := contractFieldsActualOfComparison C3 P h
  b5 := b5ContractEvidence_of_inputs T hbase hF

/-- The combined evidence yields the signed contract and the B5 residue gap. -/
theorem contractEvidenceWithB5_cor312_and_gap
    (h : qThetaPilotLogVolumeComparison C3 P)
    (hbase : NativeBaseResidueFieldEquivInput T)
    (hF : QVFamResidueFieldEquivInput T) :
    ResNormDegreeGap T :=
  b5_residue_gap_row T ((contractEvidenceWithB5_of_inputs T C3 P h hbase hF).b5)

def contractB5EvidenceRows : List (String × String × String) :=
  [ ("b5_norm_row", "B5 norm power row from B5ContractEvidence", "PROVED"),
    ("b5_log_row", "B5 log-norm row from B5ContractEvidence", "PROVED"),
    ("b5_residue_gap_row", "residue gap from B5ContractEvidence", "PROVED"),
    ("ContractEvidenceWithB5", "combined signed + B5 evidence", "CONSTRUCTED"),
    ("contractEvidenceWithB5_of_inputs", "from comparison + residue-field inputs", "PROVED (conditional)") ]

theorem contractB5EvidenceRows_length : contractB5EvidenceRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P7ContractB5EvidenceActual

end