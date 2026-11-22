import tmp.sheaf.xif.paper.S3131QCLeHCComparisonActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.QVFamPureFractionalScalingDataGapActual

/-! # S3131: identification of the native q-side reading and Q_C <= H_C

S3131QCLeHCComparisonActual proved the Batch A comparison for the actual
regional readouts:

  S3131RegionalQC <= S3131RegionalHC,

where the q side is the q-pilot region log-volume qPilotNormRegion
(actual normalized qVFamily coefficient) and the hull side is the actual
nonzero root Theta hull paperRootThetaHullNonzero (IUT III Corollary 3.12,
corpus lines 10326-10338; Step (xi-d), lines 10823-10860).

This file identifies the q-side region readout with the native q-side scalar

  S3131QC = nativeQVPilotNormalizedSignedLogVolume
(the actual clause-B qVFamily readout of S3130QCSourceActual, see
S3131QCActualReadout) at every bad place, and concludes

  Q_C <= H_C  for the native reading

under the exact remaining actual object:

  QVFamNormalizedCoefficientGap b :
    qVFamNormalizedCoefficient T b = qVFamPureCoefficient T b ()

i.e. the equality of the actual normalized (spectral CommonPrimeCompletion)
coefficient and the actual default-completion-norm coefficient of the SAME
qVFamily element.  The tree constructs both coefficients and the normalized
pure-fractional scaling data (QVFamNormalizedGeneratorSupplyActual:54-149) and
proves the normalized generator norm identity, but it supplies no equality of
the two completion norm instances on the qVFamily element; that equality is
registered there as QVFamNormalizedCoefficientGap (:151-154) and is the exact
named remaining object.  It is NOT assumed here; the main theorem takes it as
an explicit hypothesis and every other ingredient is proved.

No sorry/axiom/True/PUnit.  The two sides are not the same average.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3131NativeQCIdentificationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S3131SameCSourceInputActual
open LeanFormal.IUT.XiFPaper.S3131QCActualReadout
open LeanFormal.IUT.XiFPaper.S3131HullActualReadout
open LeanFormal.IUT.XiFPaper.S3131QCLeHCComparisonActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [forall b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [forall b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
variable (mu : forall b : Bad (nativePlaceSelection T),
  Measure (qVFamTensorBlock T b))
variable [forall b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-- The actual default-norm qVFamily coefficient times log p is the actual
qVFamily local log magnitude (definition of logb and of the local signed log). -/
theorem S3131PureCoefficient_mul_log (b : Bad (nativePlaceSelection T)) :
    qVFamPureCoefficient T b () * Real.log (qVFamTensorP T b : Real) =
      nativeQVPilotLocalMagnitude (l := l) T b := by
  have hprime : Nat.Prime (qVFamTensorP T b) :=
    Fact.out (p := Nat.Prime (qVFamTensorP T b))
  have hp1 : (1 : Real) < (qVFamTensorP T b : Real) := by exact_mod_cast hprime.one_lt
  have hp0 : (0 : Real) < (qVFamTensorP T b : Real) := lt_trans zero_lt_one hp1
  have hlogp : Real.log (qVFamTensorP T b : Real) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hp0 (ne_of_gt hp1)
  have hunit : ‖(qVFamDefaultCompletionUnit (l := l) T b :
      Completion ((nativeBadLift T).lift b))‖ = ‖(qVFamily T b).q‖ :=
    rfl
  unfold qVFamPureCoefficient nativeQVPilotLocalMagnitude localLogMagnitude
    localSignedLog
  rw [hunit]
  unfold Real.logb
  field_simp [hlogp]

/-- Per-place identification: the actual q-pilot region readout is minus the
actual native qVFamily local log magnitude, under the exact registered
coefficient norm-instance identification. -/
theorem S3131LocalQ_eq_neg_nativeMagnitude (b : Bad (nativePlaceSelection T))
    (hgap : QVFamNormalizedCoefficientGap T b) :
    S3131LocalQReadout (l := l) T mu b =
      -nativeQVPilotLocalMagnitude (l := l) T b := by
  rw [S3131LocalQ_eq_formula]
  congr 1
  have hfam : (fun i : qVFamTensorV => rootNormCoefficient (l := l) T b i) =
      qVFamPureCoefficient T b := by
    funext i
    have h1 : rootNormCoefficient (l := l) T b i = qVFamNormalizedCoefficient T b := by
      simp [rootNormCoefficient, qVFamNormalizedCoefficientFamily]
    rw [h1, hgap]
  rw [hfam]
  have hsingle : (∑ i : qVFamTensorV, qVFamPureCoefficient T b i) =
      qVFamPureCoefficient T b () := by
    simp only [qVFamTensorV, Finset.univ_unique, Finset.sum_singleton]
  rw [hsingle]
  exact S3131PureCoefficient_mul_log (l := l) T b

/-- **Same-C identification of the two readings.** Under the exact registered
coefficient norm-instance identification at every bad place, the actual q-side
region readout is the native q-side scalar S3131QC computed from the same
qVFamily family. -/
theorem S3131RegionalQC_eq_nativeQC
    (hgap : forall b : Bad (nativePlaceSelection T),
      QVFamNormalizedCoefficientGap T b) :
    S3131RegionalQC (l := l) T mu = S3131QC (l := l) T := by
  have hper : forall b : Bad (nativePlaceSelection T),
      S3131LocalQReadout (l := l) T mu b =
        -nativeQVPilotLocalMagnitude (l := l) T b :=
    fun b => S3131LocalQ_eq_neg_nativeMagnitude (l := l) T mu b (hgap b)
  unfold S3131RegionalQC
  rw [show S3131QC (l := l) T =
      -(∑ b : Bad (nativePlaceSelection T),
          nativeBadLocalWeight T b * nativeQVPilotLocalMagnitude (l := l) T b)
      from rfl]
  simp only [hper, mul_neg]
  rw [Finset.sum_neg_distrib]

/-- **Batch A main theorem for the native q-side reading.** Under the exact
registered coefficient norm-instance identification, the native actual q-side
reading Q_C = nativeQVPilotNormalizedSignedLogVolume is at most the actual
Theta-hull readout H_C of the same fixed input C. -/
theorem S3131QC_le_RegionalHC
    (hgap : forall b : Bad (nativePlaceSelection T),
      QVFamNormalizedCoefficientGap T b)
    (hsub : forall b : Bad (nativePlaceSelection T),
      S3131QRegionContainedInHull (l := l) T b) :
    S3131QC (l := l) T ≤ S3131RegionalHC (l := l) T mu := by
  rw [← S3131RegionalQC_eq_nativeQC (l := l) T mu hgap]
  exact S3131RegionalQC_le_RegionalHC (l := l) T mu hsub

/-- The native q-side reading is nonpositive (a signed log-volume). -/
theorem S3131QC_nonpos' : S3131QC (l := l) T ≤ 0 :=
  S3131QC_nonpos (l := l) T

/-! ## Sign bridge for the native reading -/

/-- The native q-side reading is a signed log-volume; the comparison with the
actual Theta-hull readout is equivalent to the paper's magnitude inequality
|log Theta| <= |log q|. -/
theorem S3131QC_le_RegionalHC_iff_magnitude
    (hgap : forall b : Bad (nativePlaceSelection T),
      QVFamNormalizedCoefficientGap T b)
    (hsub : forall b : Bad (nativePlaceSelection T),
      S3131QRegionContainedInHull (l := l) T b) :
    S3131QC (l := l) T ≤ S3131RegionalHC (l := l) T mu ↔
      S3131RegionalHCMagnitude (l := l) T mu ≤ -S3131QC (l := l) T := by
  unfold S3131RegionalHCMagnitude
  constructor <;> intro h <;> linarith

#print axioms S3131PureCoefficient_mul_log
#print axioms S3131LocalQ_eq_neg_nativeMagnitude
#print axioms S3131RegionalQC_eq_nativeQC
#print axioms S3131QC_le_RegionalHC

end LeanFormal.IUT.XiFPaper.S3131NativeQCIdentificationActual

end
