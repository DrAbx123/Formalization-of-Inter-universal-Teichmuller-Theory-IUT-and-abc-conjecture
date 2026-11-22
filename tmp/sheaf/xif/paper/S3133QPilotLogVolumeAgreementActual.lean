import tmp.sheaf.xif.paper.S3133QPilotIdealFamilyObjectActual
import tmp.sheaf.xif.paper.S3133RealifiedQPilotLogVolumeActual
import tmp.sheaf.xif.paper.S3133QPilotReadoutActual
import tmp.sheaf.xif.paper.S3133QPilotBatchAInputActual

/-!
# Agreement of the actual q-pilot log-volume readings on one input

Source: IUT III, Definition 3.8, (i), pp. 112-113; §3, p. 16 (iut3.txt lines
880-893): the q-pilot object is determined by the q_v, v in V_bad, and its
log-volume is -|log q| in R.  IUT III, Remark 3.1.1, (ii)-(iv), p. 95-97: the
procession-normalized log-volume is the weighted sum with weights 1/N_v.
IUT III, Step (xi), p. 180-183: the represented q-pilot log-volume is -|log q|.

This file records, for one fixed input X, that the actual constructions of the
q-pilot object/log-volume built in this stream are read off the SAME actual
qVFamily and agree:

1. the presentation-level arithmetic line-bundle object O(-D_q)
   (S3133QPilotIdealFamilyObjectActual) has divisor class equal to the
   Grothendieck class of the actual q_v zero-locus divisor D_q;
2. the carrier-level realified divisor on C^boxplus_mod
   (S3133RealifiedQPilotDivisorActual) has log-volume equal to the
   presentation-level q-pilot log-volume qPilotQGlobalLogVolume;
3. qPilotQGlobalLogVolume is minus the classical q-pilot log, and equals the
   sum of the actual signed q_v logarithms;
4. the Batch A Q_C source readout (S3133QPilotReadoutActual /
   S3133QPilotBatchAInputActual) at each bad place is the signed log of the
   actual qVFamily q, and its procession-normalized value is the actual native
   q-pilot scalar -|log q|.

No inequality is asserted.  No toy/True/PUnit/axiom/sorry.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133QPilotLogVolumeAgreementActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.S3133QPilotIdealFamilyObjectActual
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3133QPilotReadoutActual
open LeanFormal.IUT.XiFPaper.S3133QPilotBatchAInputActual
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalObjectActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.QPilotClassicalLogActual
open LeanFormal.IUT.XiFPaper.QVFamThetaImageActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]

/-- The presentation-level q-pilot arithmetic line-bundle object has the divisor
class of the actual q_v zero-locus divisor, and its log-volume is the actual
q-pilot global log-volume. -/
theorem qPilotLineBundleObject_sameInput :
    (qPilotLineBundleObject X).divisorClass =
        Algebra.GrothendieckAddGroup.of (qVZeroLocusQEffectiveGlobal X) ∧
      qPilotQGlobalLogVolume X =
        -∑ b : Bad (nativePlaceSelection X.S),
          localLogMagnitude (qVFamily X.S b) :=
  qPilotLineBundleObject_logVolume_link X

/-- The carrier-level realified q-pilot divisor has the same log-volume as the
presentation-level q-pilot log-volume. -/
theorem realified_presentation_logVolume_agreement :
    qPilotRealifiedLogVolume X = qPilotQGlobalLogVolume X :=
  qPilotRealifiedLogVolume_eq_qPilotQGlobalLogVolume X

/-- The q-pilot global log-volume is minus the classical q-pilot log of the same
actual q_v family. -/
theorem qPilotGlobalLogVolume_eq_neg_classicalLog :
    qPilotQGlobalLogVolume X = -qPilotClassicalLog X := by
  rw [qPilotClassicalLog_eq_neg_globalLogVolume, neg_neg]

/-- The realified q-pilot log-volume is the sum of the actual signed q_v
logarithms of the same input. -/
theorem realified_logVolume_eq_sum_localSignedLog :
    qPilotRealifiedLogVolume X =
      ∑ b : Bad (nativePlaceSelection X.S),
        localSignedLog (qVFamily X.S b) :=
  qPilotRealifiedLogVolume_eq_sum_localSignedLog X

/-- Every per-place Batch A Q_C readout is the signed log of the same actual
qVFamily q and equals minus the actual q_v log-magnitude. -/
theorem qCReadout_eq_signedQVFam
    (h : ∀ b : Bad (nativePlaceSelection X.S),
      S2135PrimeAlignmentRequired X.S b)
    (b : Bad (nativePlaceSelection X.S)) :
    qPilotSignedReadoutAt X b (h b) = qVFamilySignedLog X.S b ∧
      qPilotSignedReadoutAt X b (h b) =
        -localLogMagnitude (qVFamily X.S b) :=
  ⟨qPilotSignedReadoutAt_eq_qVFamilySignedLog X b (h b),
    qPilotSignedReadoutAt_eq_neg_localLogMagnitude X b (h b)⟩

/-- The procession-normalized Batch A Q_C readout is the actual native q-pilot
scalar -|log q| of the same input. -/
theorem batchA_QC_eq_normalizedQPilot
    (h : ∀ b : Bad (nativePlaceSelection X.S),
      S2135PrimeAlignmentRequired X.S b) :
    qPilotNormalizedGlobalReadout X h =
      nativeQVPilotNormalizedSignedLogVolume X.S :=
  qPilotNormalizedGlobalReadout_eq X h

/-- The agreement package for one fixed input: the line-bundle object's divisor
class is the q_v zero-locus class, and the realified, presentation-level,
classical and Batch A readings of the q-pilot log-volume are read off the same
actual q_v family. -/
theorem qPilotLogVolume_sameInput_package
    (h : ∀ b : Bad (nativePlaceSelection X.S),
      S2135PrimeAlignmentRequired X.S b) :
    (qPilotLineBundleObject X).divisorClass =
        Algebra.GrothendieckAddGroup.of (qVZeroLocusQEffectiveGlobal X) ∧
      qPilotRealifiedLogVolume X = qPilotQGlobalLogVolume X ∧
      qPilotRealifiedLogVolume X =
        ∑ b : Bad (nativePlaceSelection X.S),
          localSignedLog (qVFamily X.S b) ∧
      qPilotNormalizedGlobalReadout X h =
        nativeQVPilotNormalizedSignedLogVolume X.S :=
  ⟨(qPilotLineBundleObject_sameInput X).1,
    realified_presentation_logVolume_agreement X,
    realified_logVolume_eq_sum_localSignedLog X,
    batchA_QC_eq_normalizedQPilot X h⟩

end LeanFormal.IUT.XiFPaper.S3133QPilotLogVolumeAgreementActual
