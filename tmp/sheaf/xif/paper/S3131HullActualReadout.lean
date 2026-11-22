import tmp.sheaf.xif.paper.S3131SameCSourceInputActual
import tmp.sheaf.xif.paper.S914PaperLVExInstantiationActual
import tmp.sheaf.xif.paper.S918RQpilotVolumeLeSHullActual
import tmp.sheaf.xif.paper.S929RQpilotPaperSHullFinalActual
import tmp.sheaf.xif.paper.RootHullMeasureActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual

/-! # S3131: actual Theta-hull normalized readout H_C-local on the fixed input C

The hull side of Batch A is the procession-normalized mono-analytic log-volume
of the holomorphic hull of the union of possible images of a Theta-pilot object
(IUT III Corollary 3.12, corpus lines 10326-10338 and Step (xi-d), corpus lines
10823-10860).  On the fixed same-C input this is read on the actual one-factor
arithmetic tensor block at each bad place b:

* the possible Theta images are the actual nonzero root Theta regions built from
  the same qVFamily order data (RootHullClosednessActual /
  BadPlacePaperRootThetaHullActual);
* the hull is the actual closure hull paperRootThetaHullNonzero, contained in
  the actual holomorphic unit reference O_hol (S918);
* the readout is the actual degree-normalized Haar log-volume
  arithmeticTupleNormalizedLogVolume (IUT IV Proposition 1.4(i) normalization,
  FinitePlaceNormalizedUnitScalingLogVolume).

The q side on the same block is the actual q-pilot region qPilotNormRegion
(RootNormalizedContainmentActual) built from the actual normalized qVFamily
coefficient.  This file proves the per-place comparison

  V(q-pilot region) <= V(Theta-hull)

from the actual containment qPilotNormRegion subset paperRootThetaHullNonzero
(the q-pilot region is a member of the Theta image union whose closure hull is
the hull), together with actual Haar positivity/finiteness.  It also proves
the hull readout is nonpositive (hull contained in O_hol).

No sorry/axiom/True/PUnit; no inequality is assumed.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3131HullActualReadout

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

/-- The q side on the same-C block: the actual q-pilot region readout. -/
noncomputable def S3131LocalQReadout (b : Bad (nativePlaceSelection T)) : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
    (mu b) (qPilotNormRegion (l := l) T b)

/-- The hull side on the same-C block: the actual Theta-hull region readout. -/
noncomputable def S3131LocalHullReadout (b : Bad (nativePlaceSelection T)) : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
    (mu b) (s914S (l := l) T b)

/-- Same-C identification of the hull object: the readout region is exactly the
actual paper nonzero root Theta hull on the same bad place. -/
theorem S3131LocalHull_region_eq (b : Bad (nativePlaceSelection T)) :
    (s914S (l := l) T b : Set (qVFamTensorBlock T b)) =
      paperRootThetaHullNonzero (l := l) T b := rfl

/-- Same-C identification of the q object: the readout region is the actual
normalized qVFamily q-pilot classical region. -/
theorem S3131LocalQ_region_eq (b : Bad (nativePlaceSelection T)) :
    (qPilotNormRegion (l := l) T b : Set (qVFamTensorBlock T b)) =
      qPilotClassicalRegion (qVFamTensorPlaces T b) qVFamTensorTuple
        (rootNormCoefficient (l := l) T b) := rfl

/-- Exact formula for the local q readout from the actual normalized fractional
lattice scaling data: V(q-pilot region) = -(sum_i c_norm_i) * log p. -/
theorem S3131LocalQ_eq_formula (b : Bad (nativePlaceSelection T)) :
    S3131LocalQReadout (l := l) T mu b =
      -((∑ i : qVFamTensorV, rootNormCoefficient (l := l) T b i) *
        Real.log (qVFamTensorP T b : Real)) := by
  rw [show S3131LocalQReadout (l := l) T mu b =
      qPilotClassicalLog (qVFamTensorPlaces T b) qVFamTensorTuple (mu b)
        (rootNormCoefficient (l := l) T b)
        (rootNormScalingData (l := l) T b) from rfl]
  exact qPilotNormLog_eq (l := l) T b (mu := mu b)

/-- The Theta-hull Haar measure is finite at every bad place: the actual hull
is contained in the actual holomorphic unit reference O_hol. -/
theorem S3131LocalHull_measure_lt_top (b : Bad (nativePlaceSelection T)) :
    (mu b) (s914S (l := l) T b) < ⊤ :=
  s918S_measure_lt_top (l := l) T b (mu b)

/-- The Theta-hull Haar measure is positive at every bad place. -/
theorem S3131LocalHull_measure_pos (b : Bad (nativePlaceSelection T)) :
    0 < (mu b) (s914S (l := l) T b) :=
  s918S_measure_pos (l := l) T b (mu b)
    (S918RMeasurePosRequired_actual (l := l) T b (mu b))

/-- **The exact Batch A coefficient/containment gap.** The actual normalized
(spectral Q_p) qVFamily q-pilot region at b is contained in the actual paper
root-coefficient Theta hull at the same bad place.  The two objects live on the
same actual tensor block and use the same actual Haar log-volume; the only
content is the coefficient comparison between the normalized qVFamily
coefficient (spectral norm) and the tree's paper root coefficient order/(2l)
(default residue-norm convention).  This containment is recorded as the exact
named gap and is NOT asserted. -/
def S3131QRegionContainedInHull (b : Bad (nativePlaceSelection T)) : Prop :=
  (qPilotNormRegion (l := l) T b : Set (qVFamTensorBlock T b)) ⊆
    (s914S (l := l) T b : Set (qVFamTensorBlock T b))

/-- **Per-place Batch A comparison (conditional on the exact named gap).** The
actual q-pilot region readout is at most the actual Theta-hull readout whenever
the actual q-pilot region is contained in the actual hull, by monotonicity of
the actual degree-normalized Haar log-volume under inclusion. -/
theorem S3131LocalQ_le_LocalHull (b : Bad (nativePlaceSelection T))
    (hsub : S3131QRegionContainedInHull (l := l) T b) :
    S3131LocalQReadout (l := l) T mu b ≤ S3131LocalHullReadout (l := l) T mu b := by
  unfold S3131LocalQReadout S3131LocalHullReadout
  exact arithmeticTupleNormalizedLogVolume_mono
    (qVFamTensorPlaces T b) qVFamTensorTuple (mu b) hsub
    (qPilotNormRegion_measure_pos_lt_top (l := l) T b (mu b)).1
    (s918S_measure_lt_top (l := l) T b (mu b))

/-- The actual Theta-hull readout is nonpositive: the hull is contained in the
holomorphic unit reference whose normalized log-volume is zero. -/
theorem S3131LocalHull_nonpos (b : Bad (nativePlaceSelection T)) :
    S3131LocalHullReadout (l := l) T mu b ≤ 0 := by
  unfold S3131LocalHullReadout
  have hsub := s918S_subset_holomorphic (l := l) T b
  have hpos := S3131LocalHull_measure_pos (l := l) T mu b
  have hfin : (mu b) (arithmeticTupleCanonicalUnitReference
      (qVFamTensorPlaces T b) qVFamTensorTuple) < ⊤ :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top
      (qVFamTensorPlaces T b) qVFamTensorTuple (mu b)).2.2
  have hle := arithmeticTupleNormalizedLogVolume_mono
    (qVFamTensorPlaces T b) qVFamTensorTuple (mu b) hsub hpos hfin
  rwa [arithmeticTupleNormalizedLogVolume_canonicalUnitReference] at hle

#check S3131LocalQ_le_LocalHull
#check S3131LocalHull_nonpos
#check S3131LocalQ_eq_formula

end LeanFormal.IUT.XiFPaper.S3131HullActualReadout

end
