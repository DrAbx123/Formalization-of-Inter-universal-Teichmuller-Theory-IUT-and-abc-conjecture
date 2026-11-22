import tmp.sheaf.xif.paper.S3130QCSourceActual
import tmp.sheaf.xif.paper.QVFamThetaImageActual
import tmp.sheaf.xif.paper.QPilotGlobalLogVolumeFromQActual
import tmp.sheaf.xif.paper.QPilotClassicalLogActual
import tmp.sheaf.xif.paper.NativeQVPilotNormalizedLogVolumeActual

/-!
# The q-pilot log-volume reading from the actual Q_C source data

Source: IUT III, Definition 3.8, (i), pp. 112-113 and §3, p. 16 (iut3.txt lines
880-893): the q-pilot object is determined by the q_v, v in V_bad, and its
log-volume is -|log q| in R, with |log q| > 0.  IUT III, Remark 3.1.1, (ii)-(iv),
p. 95-97 (iut3.txt lines 5590-5747): the procession-normalized log-volume of a
direct product region is the weighted sum of the local log-volumes with
normalization weights 1/N_v, N_v = product of the completion degrees
[K_{v_alpha} : (F_mod)_{v_alpha}].  IUT III, Step (xi), p. 180-183 (iut3.txt
lines 10988-11034): the log-volume of the region representing the q-pilot object
on the 1-column is -|log q|.

For a fixed bad place b and the actual paper prime alignment h, the signed q
readout of the actual Q_C source data (S3130QCSourceActual) is

  qPilotSignedReadoutAt b h := localSignedLog ((s3130QCSourceData b h).qV).

It is proved to be exactly the signed q-pilot log-volume of the same actual q_v
family: equal to Real.log of the source qNorm, equal to -|log q_v(b)|, with
magnitude the paper form mult_b * log(residueNormBase b).  The finite weighted
global readout with the actual Remark 3.1.1 place weights is exactly the actual
procession-normalized q-pilot log-volume nativeQVPilotNormalizedSignedLogVolume
(the scalar called Q_C by the Batch A mainline); with unit weights it is the
unweighted q-pilot log-volume qPilotQGlobalLogVolume = -qPilotClassicalLog.

No inequality is asserted.  No toy/True/PUnit/axiom/sorry.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133QPilotReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual
open LeanFormal.IUT.XiFPaper.S3130QCSourceActual
open LeanFormal.IUT.XiFPaper.QVFamThetaImageActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.QPilotClassicalLogActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- The signed q-pilot log reading at a fixed bad place, computed from the actual
Q_C source data of the same input. -/
noncomputable def qPilotSignedReadoutAt
    (b : Bad (nativePlaceSelection X.S))
    (h : S2135PrimeAlignmentRequired X.S b) : Real :=
  localSignedLog ((s3130QCSourceData X.S b h).qV)

/-- The signed readout from the Q_C source is the signed log of the actual
qVFamily q: both use the same clause-B q candidate. -/
theorem qPilotSignedReadoutAt_eq_qVFamilySignedLog
    (b : Bad (nativePlaceSelection X.S))
    (h : S2135PrimeAlignmentRequired X.S b) :
    qPilotSignedReadoutAt X b h = qVFamilySignedLog X.S b := rfl

/-- The signed readout is exactly the log of the actual source qNorm. -/
theorem qPilotSignedReadoutAt_eq_log_qNorm
    (b : Bad (nativePlaceSelection X.S))
    (h : S2135PrimeAlignmentRequired X.S b) :
    qPilotSignedReadoutAt X b h =
      Real.log ((s3130QCSourceData X.S b h).qNorm) := rfl

/-- The signed readout is minus the actual q_v log-magnitude -|log q_v|. -/
theorem qPilotSignedReadoutAt_eq_neg_localLogMagnitude
    (b : Bad (nativePlaceSelection X.S))
    (h : S2135PrimeAlignmentRequired X.S b) :
    qPilotSignedReadoutAt X b h =
      -localLogMagnitude (qVFamily X.S b) := by
  rw [qPilotSignedReadoutAt_eq_qVFamilySignedLog X b h,
    qVFamilySignedLog_eq_neg_magnitude]

/-- The signed q readout is negative: the actual q_v is contracting. -/
theorem qPilotSignedReadoutAt_neg
    (b : Bad (nativePlaceSelection X.S))
    (h : S2135PrimeAlignmentRequired X.S b) :
    qPilotSignedReadoutAt X b h < 0 := by
  rw [qPilotSignedReadoutAt_eq_qVFamilySignedLog X b h]
  exact localSignedLog_neg (qVFamily X.S b)

/-- The paper form of the actual q_v log-magnitude: multiplicity times the log of
the actual residue norm base (IUT III, p. 124, log(q) = ord_v(q_v) log(p_v)). -/
theorem qPilotLogMagnitudeAt_eq_multiplicity_mul_log
    (b : Bad (nativePlaceSelection X.S)) :
    localLogMagnitude (qVFamily X.S b) =
      (qVEffectiveMultiplicity X b : Real) * Real.log (residueNormBase b.1) :=
  qVFamily_localLogMagnitude_eq X b

/-- The finite weighted global q-pilot readout: the weighted sum of the actual
Q_C source readouts with place weights w. -/
noncomputable def qPilotWeightedGlobalReadout
    [Fintype (Bad (nativePlaceSelection X.S))]
    (w : Bad (nativePlaceSelection X.S) → Real)
    (h : ∀ b : Bad (nativePlaceSelection X.S),
      S2135PrimeAlignmentRequired X.S b) : Real :=
  ∑ b : Bad (nativePlaceSelection X.S), w b * qPilotSignedReadoutAt X b (h b)

/-- The unit-weight global readout is the actual unweighted q-pilot log-volume
-|log q| of QPilotGlobalLogVolumeFromQActual. -/
theorem qPilotWeightedGlobalReadout_one
    [Fintype (Bad (nativePlaceSelection X.S))]
    (h : ∀ b : Bad (nativePlaceSelection X.S),
      S2135PrimeAlignmentRequired X.S b) :
    qPilotWeightedGlobalReadout X (fun _ => 1) h = qPilotQGlobalLogVolume X := by
  rw [qPilotWeightedGlobalReadout, qPilotQGlobalLogVolume_eq_neg_sum_qVLogMagnitude]
  simp only [one_mul]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl
    (fun b _ => qPilotSignedReadoutAt_eq_neg_localLogMagnitude X b (h b))

/-- The actual procession-normalized q-pilot log-volume: the weighted sum of the
Q_C source readouts with the actual Remark 3.1.1 place weights. -/
noncomputable def qPilotNormalizedGlobalReadout
    [Fintype (Bad (nativePlaceSelection X.S))]
    (h : ∀ b : Bad (nativePlaceSelection X.S),
      S2135PrimeAlignmentRequired X.S b) : Real :=
  qPilotWeightedGlobalReadout X (nativeBadLocalWeight X.S) h

/-- The procession-normalized q-pilot log-volume read off the Q_C source is
exactly the actual native normalized q-pilot scalar -|log q|. -/
theorem qPilotNormalizedGlobalReadout_eq
    [Fintype (Bad (nativePlaceSelection X.S))]
    (h : ∀ b : Bad (nativePlaceSelection X.S),
      S2135PrimeAlignmentRequired X.S b) :
    qPilotNormalizedGlobalReadout X h =
      nativeQVPilotNormalizedSignedLogVolume X.S := by
  unfold qPilotNormalizedGlobalReadout qPilotWeightedGlobalReadout
    nativeQVPilotNormalizedSignedLogVolume nativeQVPilotNormalizedLogMagnitude
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [qPilotSignedReadoutAt_eq_neg_localLogMagnitude]
  simp only [nativeQVPilotLocalMagnitude]
  ring

/-- The procession-normalized q-pilot log-volume is nonpositive. -/
theorem qPilotNormalizedGlobalReadout_nonpos
    [Fintype (Bad (nativePlaceSelection X.S))]
    (h : ∀ b : Bad (nativePlaceSelection X.S),
      S2135PrimeAlignmentRequired X.S b) :
    qPilotNormalizedGlobalReadout X h <= 0 := by
  rw [qPilotNormalizedGlobalReadout_eq X h]
  exact neg_nonpos.mpr (nativeQVPilotNormalizedLogMagnitude_nonneg X.S)

end LeanFormal.IUT.XiFPaper.S3133QPilotReadoutActual
