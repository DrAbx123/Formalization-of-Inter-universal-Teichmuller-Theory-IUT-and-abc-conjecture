import tmp.sheaf.xif.paper.S3131SameCSourceInputActual

/-! # S3131: actual q-side reading Q_C on the fixed input C

Q_C is the procession-normalized signed mono-analytic log-volume of the image
of the q-pilot object (IUT III Corollary 3.12, corpus lines 10340-10345).  On the
fixed same-C input of S3131SameCSourceInputActual it is the actual clause-B
qVFamily readout with the actual Remark 3.1.1(ii) place weights:

  Q_C = - sum_b w_b * localLogMagnitude(qVFamily b).

This file proves:

* the exact expanded formula (S3131QC_eq_formula);
* nonpositivity Q_C <= 0 (S3131QC_nonpos), the sign of a log-volume;
* the same-C identification with the actual q-side source data family
  (S3131QC_eq_sourceData_signedSum, S3131QC_eq_sourceData_normLog): every term
  is the signed log of the very same (qSourceFamily hAlign b).qV whose
  provenance is registered in S3130QCSourceActual.

No inequality between Q_C and a hull is asserted here.  No sorry/axiom/toy.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3131QCActualReadout

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.S3130QCSourceActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.QVFamThetaImageActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S3131SameCSourceInputActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Q_C: the actual q-side signed mono-analytic log readout on the fixed input
C, computed from the actual clause-B qVFamily family and the actual Remark
3.1.1(ii) place weights. -/
noncomputable def S3131QC : Real :=
  nativeQVPilotNormalizedSignedLogVolume T

/-- Exact weighted formula of the actual q-side reading. -/
theorem S3131QC_eq_formula :
    S3131QC T =
      -(∑ b : Bad (nativePlaceSelection T),
          nativeBadLocalWeight T b * nativeQVPilotLocalMagnitude T b) := rfl

/-- Q_C is the signed readout of the actual local magnitudes. -/
theorem S3131QC_eq_neg_normalizedMagnitude :
    S3131QC T = -nativeQVPilotNormalizedLogMagnitude T := rfl

/-- Q_C is nonpositive: it is a signed log-volume. -/
theorem S3131QC_nonpos : S3131QC T ≤ 0 := by
  unfold S3131QC nativeQVPilotNormalizedSignedLogVolume
  exact neg_nonpos.mpr (nativeQVPilotNormalizedLogMagnitude_nonneg T)

/-- Same-C identification: Q_C reads exactly the signed log of the actual
q-side source data (qSourceFamily hAlign b).qV at every bad place. -/
theorem S3131QC_eq_sourceData_signedSum
    (hAlign : forall b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired T b) :
    S3131QC T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * localSignedLog ((qSourceFamily T hAlign b).qV) := by
  rw [S3131QC_eq_formula]
  have hsum : (∑ b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b * localSignedLog ((qSourceFamily T hAlign b).qV))
      = ∑ b : Bad (nativePlaceSelection T),
          -(nativeBadLocalWeight T b * nativeQVPilotLocalMagnitude T b) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [qSourceFamily_qV T hAlign b]
    unfold nativeQVPilotLocalMagnitude
    rw [localSignedLog_eq_neg_magnitude]
    ring
  rw [hsum, Finset.sum_neg_distrib]

/-- Same-C identification, norm form: Q_C sums the log of the actual
qVFamilyQNorm of the same fixed input. -/
theorem S3131QC_eq_sourceData_normLog
    (hAlign : forall b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired T b) :
    S3131QC T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * Real.log ((qSourceFamily T hAlign b).qNorm) := by
  rw [S3131QC_eq_sourceData_signedSum T hAlign]
  apply Finset.sum_congr rfl
  intro b _
  rfl

/-- The same-C source-data form is the negative weighted sum of the actual
local norm logarithms: Q_C = - sum_b w_b * (-log qNorm(b)). -/
theorem S3131QC_eq_neg_sourceData_normLog
    (hAlign : forall b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired T b) :
    S3131QC T =
      -(∑ b : Bad (nativePlaceSelection T),
          nativeBadLocalWeight T b * (-Real.log ((qSourceFamily T hAlign b).qNorm))) := by
  rw [S3131QC_eq_sourceData_normLog T hAlign]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

#check S3131QC_eq_formula
#check S3131QC_nonpos
#check S3131QC_eq_sourceData_signedSum
#check S3131QC_eq_sourceData_normLog

end LeanFormal.IUT.XiFPaper.S3131QCActualReadout

end
