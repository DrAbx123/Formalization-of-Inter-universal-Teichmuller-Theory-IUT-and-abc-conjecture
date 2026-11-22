import tmp.sheaf.xif.paper.S3133QPilotReadoutActual
import tmp.sheaf.xif.paper.S3130QCLeHCActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual

/-!
# Batch A Q_C input from the actual procession-normalized q-pilot log-volume

Source: IUT III, Corollary 3.12, pp. 173-174 (iut3.txt lines 10516-10529); the
Batch A convention Q_C <= H_C of coord/ROADMAP-2026-11-02.md: Q_C is the signed
q-side readout -|log q| and H_C the ambient hull log-volume.

This file instantiates the Batch A datum S3130QCLeHCData (S3130QCLeHCActual) on
the fixed qualified input, with

* the signed q readout Q_C := the actual procession-normalized q-pilot
  log-volume qPilotNormalizedGlobalReadout (S3133QPilotReadoutActual), which is
  exactly the actual native q-pilot scalar -|log q|;
* the ambient hull interface W of the same input as the hull datum.

The Q_C readout is independent of W, which records the same-input condition of
Batch A.  The comparison Q_C <= H_C itself is NOT asserted: it remains the
mainline S3130QCLeHCGap.  No toy/True/PUnit/axiom/sorry.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133QPilotBatchAInputActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual
open LeanFormal.IUT.XiFPaper.S3130QCLeHCActual
open LeanFormal.IUT.XiFPaper.S3133QPilotReadoutActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- The Batch A Q_C datum on the fixed qualified input, with the actual
procession-normalized q-pilot log-volume -|log q| as its signed q readout and the
ambient hull interface W of the same input as its hull datum. -/
noncomputable def qPilotBatchAInput
    {Xc : Type u} (W : IQHullLogVolumeInterface Xc)
    [Fintype (Bad (nativePlaceSelection X.S))]
    (h : ∀ b : Bad (nativePlaceSelection X.S),
      S2135PrimeAlignmentRequired X.S b) :
    S3130QCLeHCData Xc where
  W := W
  qReadout := qPilotNormalizedGlobalReadout X h

/-- The Q_C readout of the Batch A input is the procession-normalized q-pilot
log-volume. -/
theorem qPilotBatchAInput_QC
    {Xc : Type u} (W : IQHullLogVolumeInterface Xc)
    [Fintype (Bad (nativePlaceSelection X.S))]
    (h : ∀ b : Bad (nativePlaceSelection X.S),
      S2135PrimeAlignmentRequired X.S b) :
    (qPilotBatchAInput X W h).QC = qPilotNormalizedGlobalReadout X h := rfl

/-- The Batch A Q_C readout equals the actual native normalized q-pilot scalar
-|log q|. -/
theorem qPilotBatchAInput_QC_eq_normalized
    {Xc : Type u} (W : IQHullLogVolumeInterface Xc)
    [Fintype (Bad (nativePlaceSelection X.S))]
    (h : ∀ b : Bad (nativePlaceSelection X.S),
      S2135PrimeAlignmentRequired X.S b) :
    (qPilotBatchAInput X W h).QC =
      nativeQVPilotNormalizedSignedLogVolume X.S :=
  qPilotNormalizedGlobalReadout_eq X h

/-- The Batch A Q_C readout is the negative weighted sum of the actual q_v log
magnitudes, i.e. the paper procession-normalized -|log q|. -/
theorem qPilotBatchAInput_QC_eq_neg_weightedMagnitude
    {Xc : Type u} (W : IQHullLogVolumeInterface Xc)
    [Fintype (Bad (nativePlaceSelection X.S))]
    (h : ∀ b : Bad (nativePlaceSelection X.S),
      S2135PrimeAlignmentRequired X.S b) :
    (qPilotBatchAInput X W h).QC =
      -(∑ b : Bad (nativePlaceSelection X.S),
        nativeBadLocalWeight X.S b * localLogMagnitude (qVFamily X.S b)) := by
  rw [qPilotBatchAInput_QC_eq_normalized X W h]
  unfold nativeQVPilotNormalizedSignedLogVolume nativeQVPilotNormalizedLogMagnitude
  rfl

/-- The Q_C readout of the Batch A input is independent of the chosen hull
interface: the q-pilot provenance of Q_C is a function of the same fixed input
alone (the same-input condition of Batch A). -/
theorem qPilotBatchAInput_QC_independent_of_hull
    {Xc : Type u} (W W' : IQHullLogVolumeInterface Xc)
    [Fintype (Bad (nativePlaceSelection X.S))]
    (h : ∀ b : Bad (nativePlaceSelection X.S),
      S2135PrimeAlignmentRequired X.S b) :
    (qPilotBatchAInput X W h).QC = (qPilotBatchAInput X W' h).QC := rfl

end LeanFormal.IUT.XiFPaper.S3133QPilotBatchAInputActual
