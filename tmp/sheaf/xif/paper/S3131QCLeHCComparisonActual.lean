import tmp.sheaf.xif.paper.S3131QCActualReadout
import tmp.sheaf.xif.paper.S3131HullActualReadout

/-! # S3131: Batch A comparison Q_C <= H_C on the fixed input C (regional objects)

Assembles the Batch A mainline comparison of coord/ROADMAP-2026-11-02.md section 2
on one fixed qualified input C:

* S3131RegionalQC: actual q-side region readout, the Remark 3.1.1(ii)
  weighted sum over bad places of the actual normalized q-pilot region
  log-volume qPilotNormRegion (built from the actual qVFamily data);
* S3131RegionalHC: actual Theta-hull readout, the same weighted sum of the
  actual nonzero root Theta hull log-volumes paperRootThetaHullNonzero
  (IUT III Corollary 3.12, corpus lines 10326-10338; Step (xi-d), lines
  10823-10860);
* actual nonnegative place weights nativeBadLocalWeight.

Proved here:
  S3131RegionalQC_le_RegionalHC  (given S3131QRegionContainedInHull),
i.e. the signed Batch A comparison Q_C <= H_C, from actual monotonicity of the
actual degree-normalized Haar log-volume under inclusion, summed with actual
nonnegative weights; plus nonpositivity of both readouts (regions contained in
the holomorphic unit reference O_hol), and the explicit sign bridge
  S3131RegionalQC_le_RegionalHC_iff_magnitude :
    Q_C <= H_C  <->  |log Theta| <= |log q|  (magnitude form),
so this is the genuine signed inequality, not a comparison of two nonnegative
log-volumes.

The single named gap S3131QRegionContainedInHull is exactly the coefficient
comparison between the normalized (spectral Q_p) qVFamily coefficient and the
tree's paper root coefficient order/(2l); it is NOT assumed.  The unconditional
same-coefficient version is S3131PaperNormalizedComparisonActual.  No sorry/axiom.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3131QCLeHCComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S3131SameCSourceInputActual
open LeanFormal.IUT.XiFPaper.S3131QCActualReadout
open LeanFormal.IUT.XiFPaper.S3131HullActualReadout
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

/-- The actual procession weight of a bad place is nonnegative. -/
theorem S3131Weight_nonneg (b : Bad (nativePlaceSelection T)) :
    0 ≤ nativeBadLocalWeight T b := by
  rw [nativeBadLocalWeight_eq_inv]
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Global q-side region readout on the fixed C: the actual Remark 3.1.1(ii)
weighted sum of the actual q-pilot region log-volumes. -/
noncomputable def S3131RegionalQC : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * S3131LocalQReadout (l := l) T mu b

/-- Global Theta-hull readout on the same fixed C: the actual Remark 3.1.1(ii)
weighted sum of the actual nonzero root Theta hull log-volumes. -/
noncomputable def S3131RegionalHC : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * S3131LocalHullReadout (l := l) T mu b

/-- The signed log-volume of the q side is nonpositive, given the exact named
containment gap. -/
theorem S3131LocalQ_nonpos (b : Bad (nativePlaceSelection T))
    (hsub : S3131QRegionContainedInHull (l := l) T b) :
    S3131LocalQReadout (l := l) T mu b ≤ 0 :=
  le_trans (S3131LocalQ_le_LocalHull (l := l) T mu b hsub)
    (S3131LocalHull_nonpos (l := l) T mu b)

/-- **Batch A: Q_C <= H_C on the fixed input C, for the actual regional
readouts.**  Weighted sum of the per-place comparisons under the exact named
containment gap at every bad place. -/
theorem S3131RegionalQC_le_RegionalHC
    (hsub : forall b : Bad (nativePlaceSelection T),
      S3131QRegionContainedInHull (l := l) T b) :
    S3131RegionalQC (l := l) T mu ≤ S3131RegionalHC (l := l) T mu := by
  unfold S3131RegionalQC S3131RegionalHC
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left
    (S3131LocalQ_le_LocalHull (l := l) T mu b (hsub b)) (S3131Weight_nonneg T b)

/-- The actual Theta-hull readout is nonpositive (unconditional): every local
hull is contained in the holomorphic unit reference. -/
theorem S3131RegionalHC_nonpos : S3131RegionalHC (l := l) T mu ≤ 0 := by
  unfold S3131RegionalHC
  apply Finset.sum_nonpos
  intro b _
  exact mul_nonpos_of_nonneg_of_nonpos (S3131Weight_nonneg T b)
    (S3131LocalHull_nonpos (l := l) T mu b)

/-- The q-side regional readout is nonpositive under the exact named gap. -/
theorem S3131RegionalQC_nonpos
    (hsub : forall b : Bad (nativePlaceSelection T),
      S3131QRegionContainedInHull (l := l) T b) :
    S3131RegionalQC (l := l) T mu ≤ 0 :=
  le_trans (S3131RegionalQC_le_RegionalHC (l := l) T mu hsub)
    (S3131RegionalHC_nonpos (l := l) T mu)

/-! ## Sign bridge: signed paper inequality vs magnitude inequality -/

/-- Magnitude of the local q-side reading: the nonnegative |log q|_b. -/
noncomputable def S3131LocalQMagnitude (b : Bad (nativePlaceSelection T)) : Real :=
  -S3131LocalQReadout (l := l) T mu b

/-- Magnitude of the local Theta-hull reading: |log Theta|_b. -/
noncomputable def S3131LocalHullMagnitude (b : Bad (nativePlaceSelection T)) : Real :=
  -S3131LocalHullReadout (l := l) T mu b

/-- Local q magnitude is nonnegative (under the exact named gap). -/
theorem S3131LocalQMagnitude_nonneg (b : Bad (nativePlaceSelection T))
    (hsub : S3131QRegionContainedInHull (l := l) T b) :
    0 ≤ S3131LocalQMagnitude (l := l) T mu b := by
  unfold S3131LocalQMagnitude
  linarith [S3131LocalQ_nonpos (l := l) T mu b hsub]

/-- Local hull magnitude is nonnegative. -/
theorem S3131LocalHullMagnitude_nonneg (b : Bad (nativePlaceSelection T)) :
    0 ≤ S3131LocalHullMagnitude (l := l) T mu b := by
  unfold S3131LocalHullMagnitude
  linarith [S3131LocalHull_nonpos (l := l) T mu b]

/-- **Explicit sign bridge (local).** The signed comparison of the q readout and
the Theta-hull readout is exactly the genuine signed inequality of IUT III
Corollary 3.12 in magnitude form |log Theta|_b <= |log q|_b. -/
theorem S3131LocalQ_le_LocalHull_iff_magnitude (b : Bad (nativePlaceSelection T))
    (hsub : S3131QRegionContainedInHull (l := l) T b) :
    S3131LocalQReadout (l := l) T mu b ≤ S3131LocalHullReadout (l := l) T mu b ↔
      S3131LocalHullMagnitude (l := l) T mu b ≤
        S3131LocalQMagnitude (l := l) T mu b := by
  unfold S3131LocalHullMagnitude S3131LocalQMagnitude
  constructor <;> intro h <;> linarith

/-- Global q magnitude: the nonnegative |log q| of the assembled reading. -/
noncomputable def S3131RegionalQCMagnitude : Real :=
  -S3131RegionalQC (l := l) T mu

/-- Global hull magnitude: the nonnegative |log Theta| of the assembled reading. -/
noncomputable def S3131RegionalHCMagnitude : Real :=
  -S3131RegionalHC (l := l) T mu

/-- Global q magnitude is nonnegative (under the exact named gap). -/
theorem S3131RegionalQCMagnitude_nonneg
    (hsub : forall b : Bad (nativePlaceSelection T),
      S3131QRegionContainedInHull (l := l) T b) :
    0 ≤ S3131RegionalQCMagnitude (l := l) T mu := by
  unfold S3131RegionalQCMagnitude
  linarith [S3131RegionalQC_nonpos (l := l) T mu hsub]

/-- Global hull magnitude is nonnegative (unconditional). -/
theorem S3131RegionalHCMagnitude_nonneg : 0 ≤ S3131RegionalHCMagnitude (l := l) T mu := by
  unfold S3131RegionalHCMagnitude
  linarith [S3131RegionalHC_nonpos (l := l) T mu]

/-- **Explicit sign bridge (global).** The assembled signed Batch A comparison
Q_C <= H_C is equivalent to the paper's genuine signed inequality
|log Theta| <= |log q|; it is not a comparison of two nonnegative log-volumes. -/
theorem S3131RegionalQC_le_RegionalHC_iff_magnitude
    (hsub : forall b : Bad (nativePlaceSelection T),
      S3131QRegionContainedInHull (l := l) T b) :
    S3131RegionalQC (l := l) T mu ≤ S3131RegionalHC (l := l) T mu ↔
      S3131RegionalHCMagnitude (l := l) T mu ≤
        S3131RegionalQCMagnitude (l := l) T mu := by
  unfold S3131RegionalHCMagnitude S3131RegionalQCMagnitude
  constructor <;> intro h <;> linarith

#print axioms S3131RegionalQC_le_RegionalHC
#print axioms S3131RegionalHC_nonpos
#print axioms S3131RegionalQC_le_RegionalHC_iff_magnitude

end LeanFormal.IUT.XiFPaper.S3131QCLeHCComparisonActual

end
