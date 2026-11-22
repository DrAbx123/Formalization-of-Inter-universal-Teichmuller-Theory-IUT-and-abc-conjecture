import tmp.sheaf.xif.paper.S3131QCLeHCComparisonActual
import tmp.sheaf.xif.paper.S914PaperLVExInstantiationActual
import tmp.sheaf.xif.paper.S918RQpilotVolumeLeSHullActual
import tmp.sheaf.xif.paper.S929RQpilotPaperSHullFinalActual
import tmp.sheaf.xif.paper.RootHullMeasureActual
import tmp.sheaf.xif.paper.S778PaperQPilotHalfRegionActual

/-! # S3131: paper-normalized (rooted) signed comparison Q_C <= H_C

Same fixed input C as S3131QCLeHCComparisonActual, but now with the SAME paper
root normalization on both sides:

* q side: s914R = qPilotPaperRegion, the paper q-pilot region at the root-half
  coefficient rootHalfCoefficient = (normalized q coefficient)/(2l);
* hull side: s914S = paperRootThetaHullNonzero, the actual closure hull of the
  nonzero root Theta image union built with the paper root coefficient
  order/(2l) (BadPlacePaperRootThetaHullActual).

Both regions live in the same actual one-factor arithmetic tensor block at the
same bad place b, are built from the same actual qVFamily order data, and use
the same degree-normalized Haar log-volume arithmeticTupleNormalizedLogVolume.
The actual containment s914R subset s914S is the S914/S908 OR-expansion datum
(the q-pilot region is the j = 1 member of the Theta image union).  Its Haar
positivity is the actual S929 modelHull_measure_pos; hull finiteness is the
actual S918 containment in O_hol.  Hence the per-place signed inequality

  V(q-pilot region) <= V(Theta hull)

is unconditional on actual objects and, via the explicit sign bridge, is exactly
the paper inequality |log Theta| <= |log q| in magnitude form (IUT III
Corollary 3.12, corpus lines 10324-10353).

No sorry/axiom/True/PUnit; no inequality is assumed.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3131PaperNormalizedComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.S778PaperQPilotHalfRegionActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open LeanFormal.IUT.XiFPaper.S918RQpilotVolumeLeSHullActual
open LeanFormal.IUT.XiFPaper.S929RQpilotPaperSHullFinalActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
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

/-- Paper-normalized q readout at b: the actual rooted q-pilot region
qPilotPaperRegion (coefficient rootHalfCoefficient = c_norm/(2l)). -/
noncomputable def S3131PaperQReadout (b : Bad (nativePlaceSelection T)) : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
    (mu b) (s914R (l := l) T b)

/-- Paper-normalized hull readout at b: the actual paper-coefficient non-zero
root Theta hull (-|log Theta| local signed log-volume). -/
noncomputable def S3131PaperHullReadout (b : Bad (nativePlaceSelection T)) : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
    (mu b) (s914S (l := l) T b)

/-- The hull side readout is exactly the S3131 LocalHullReadout: the same actual
Theta hull. -/
theorem S3131PaperHullReadout_eq_LocalHullReadout (b : Bad (nativePlaceSelection T)) :
    S3131PaperHullReadout (l := l) T mu b =
      S3131LocalHullReadout (l := l) T mu b := rfl

/-- **Paper-normalized per-place signed comparison.** The actual rooted q-pilot
region readout is at most the actual rooted Theta-hull readout, from the actual
OR-expansion containment s914R subset s914S and actual Haar
positivity/finiteness (discharged by S929/S918). -/
theorem S3131PaperQ_le_PaperHull (b : Bad (nativePlaceSelection T)) :
    S3131PaperQReadout (l := l) T mu b ≤ S3131PaperHullReadout (l := l) T mu b := by
  unfold S3131PaperQReadout S3131PaperHullReadout
  exact s918V_R_le_V_S (l := l) T b (mu b)
    (S918RMeasurePosRequired_actual (l := l) T b (mu b))

/-- Paper-normalized global q readout. -/
noncomputable def S3131PaperRegionalQ : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * S3131PaperQReadout (l := l) T mu b

/-- Paper-normalized global hull readout. -/
noncomputable def S3131PaperRegionalHull : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * S3131PaperHullReadout (l := l) T mu b

/-- The paper-normalized hull global readout is the S3131 regional hull readout. -/
theorem S3131PaperRegionalHull_eq_RegionalHC :
    S3131PaperRegionalHull (l := l) T mu = S3131RegionalHC (l := l) T mu := rfl

/-- **Paper-normalized global signed comparison Q_C <= H_C.** -/
theorem S3131PaperRegionalQ_le_Hull :
    S3131PaperRegionalQ (l := l) T mu ≤ S3131PaperRegionalHull (l := l) T mu := by
  unfold S3131PaperRegionalQ S3131PaperRegionalHull
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left (S3131PaperQ_le_PaperHull (l := l) T mu b)
    (S3131Weight_nonneg (l := l) T b)

/-- Magnitudes in the paper-normalized comparison. -/
noncomputable def S3131PaperQMagnitude : Real :=
  -S3131PaperRegionalQ (l := l) T mu

noncomputable def S3131PaperHullMagnitude : Real :=
  -S3131PaperRegionalHull (l := l) T mu

/-- The paper-normalized signed comparison is equivalent to the paper magnitude
inequality |log Theta| <= |log q| (same normalization on both sides). -/
theorem S3131PaperRegionalQ_le_Hull_iff_magnitude :
    S3131PaperRegionalQ (l := l) T mu ≤ S3131PaperRegionalHull (l := l) T mu ↔
      S3131PaperHullMagnitude (l := l) T mu ≤ S3131PaperQMagnitude (l := l) T mu := by
  unfold S3131PaperHullMagnitude S3131PaperQMagnitude
  constructor <;> intro h <;> linarith

#check S3131PaperQ_le_PaperHull
#check S3131PaperRegionalQ_le_Hull
#check S3131PaperRegionalQ_le_Hull_iff_magnitude

end LeanFormal.IUT.XiFPaper.S3131PaperNormalizedComparisonActual

end
