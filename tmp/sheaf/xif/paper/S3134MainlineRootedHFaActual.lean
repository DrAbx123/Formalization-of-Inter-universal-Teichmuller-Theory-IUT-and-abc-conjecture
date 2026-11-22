import tmp.sheaf.xif.paper.S3131CoefficientReductionActual
import tmp.sheaf.xif.paper.S3131QCActualReadout
import tmp.sheaf.xif.paper.S3131CanonicalRootedQCActual
import tmp.sheaf.xif.paper.S3134Step3115To312Actual

/-!
# S3134: mainline paper-faithful regional rooted comparison as the H-side signed fact

**Component, not paper object.**  This file wires the mainline stream's
unconditional paper-faithful comparison
`S3131PaperFaithfulRegionalRootedComparison`
(S3131CoefficientReductionActual:256-267) into the signed 3.11.5 => 3.12
wiring of the fourth triangle.  The paper objects are the actual q-pilot and
Theta-pilot log-volumes; this file only records the signed comparison between
them once the two actual readouts are identified.

Convention (checked against the definition, not assumed): the readouts
`qPilotPaperLog` and `rootThetaHullLog` are values of the signed
degree-normalized log-volume
`V(S) = (1/D) * (log mu(S) - log mu(O_hol))`
(IUT IV Proposition 1.4(i)); for a region inside the holomorphic lattice they
are nonpositive.  Hence the containment qPilotPaperRegion subset rootThetaHull
plus monotonicity of V gives

  V(qPilot) <= V(Theta-hull),   i.e.   -|log q| <= -|log Theta|,

which is exactly IUT III, Corollary 3.12 (corpus `III-T.txt:10352`):
`-|log Theta| >= -|log q|`.  In magnitudes: `|log Theta| <= |log q|`, i.e. the
hull magnitude is at most the q magnitude.  So this is the signed Step (xi-f)
direction, not merely the (xi-d) containment side.

What is derived here (no `S3134QThetaComparisonGap.simultaneous_comparison`
hypothesis enters):

* `S3134QThetaComparison_gap_comparison_ofMainlineRootedReadouts`:
  `H <= |log q|`, the substantive Step (xi-f) comparison, from mainline's
  unconditional actual comparison plus two *named exact* readout
  identifications;
* `S3134Step3115_ray_ofMainlineRootedReadouts`: the signed ray membership
  `-|log q| in hullLogVolumeRay (-H)`;
* `S3134Step3115_mainlineQC_le_thetaPilot_viaMainlineRooted`: the mainline
  q-side scalar bound `S3131QC T <= -|log Theta|`.

The two readout identifications are the exact remaining objects (recorded as
explicit hypotheses, never assumed):
1. mainline weighted q-pilot paper readout = `-|log q|`; this is the
   paper-normalization/coefficient identification (IUT III Remark 3.1.1(ii),
   IUT IV Proposition 1.4(i)); in the tree it is the task-13
   `QVFamNormalizedNormCompatibility` e = 1 normalization residual.
2. mainline weighted rooted Theta-hull readout = `-|log Theta|` =
   `S3134Step3115ThetaPilotReadout`; this is the Theta-side hull readout
   identification (same role as
   `MissingC3ThetaHullReadoutIdentification.hull_logVolume_eq` in hull's
   S3132QThetaConsumerWiringActual).

No sorry/axiom/arbitrary carrier; both sides are actual readouts and the
comparison is mainline's unconditional theorem.  WRITE-ONLY: no lake/lean.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S778PaperQPilotHalfRegionActual
open LeanFormal.IUT.XiFPaper.S3131CoefficientReductionActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.S3131QCActualReadout
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual
open LeanFormal.IUT.XiFPaper.S3134Step3115To312Actual
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual

universe u v uv upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{0, uv, upi, umon, ui} l V)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [forall b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [forall b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
variable (mu : forall b : Bad (nativePlaceSelection T),
  Measure (qVFamTensorBlock T b))
variable [forall b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-- The mainline unconditional paper-faithful regional rooted comparison, in
the signed degree-normalized log-volume convention (IUT III Cor 3.12 direction,
corpus `III-T.txt:10352`). -/
theorem S3134MainlineRooted_signedComparison :
    (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * qPilotPaperLog (l := l) T b (mu b)) ≤
      (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
            (mu b) (rootHalfCoefficient (l := l) T b)) :=
  S3131PaperFaithfulRegionalRootedComparison (l := l) T mu

/-- Step (xi-f) magnitude comparison `H <= |log q|`, derived from the mainline
unconditional actual comparison plus the two named exact readout
identifications (q readout = `-|log q|`, Theta readout = `-H`).  The assumed
`S3134QThetaComparisonGap.simultaneous_comparison` is NOT used. -/
theorem S3134QThetaComparison_gap_comparison_ofMainlineRootedReadouts
    (D : S1300HDDHullDetSource I)
    (hq : (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * qPilotPaperLog (l := l) T b (mu b)) =
          -|Real.log (S3134QParameter J)|)
    (hTheta : (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
            (mu b) (rootHalfCoefficient (l := l) T b)) =
          S3134Step3115ThetaPilotReadout (I := I) D) :
    S3134ThetaHullLogVolume (I := I) D ≤
      |Real.log (S3134QParameter J)| := by
  have h := S3134MainlineRooted_signedComparison (l := l) (T := T) mu
  rw [hq, hTheta] at h
  rw [S3134Step3115ThetaPilotReadout, S3134ThetaHullLogVolumeSigned] at h
  exact neg_le_neg_iff.mp h

/-- The signed Step (xi-f) ray membership `-|log q| in R_{<= -|log Theta|}`,
derived from the mainline unconditional comparison and the two readout
identifications. -/
theorem S3134Step3115_ray_ofMainlineRootedReadouts
    (D : S1300HDDHullDetSource I)
    (hq : (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * qPilotPaperLog (l := l) T b (mu b)) =
          -|Real.log (S3134QParameter J)|)
    (hTheta : (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
            (mu b) (rootHalfCoefficient (l := l) T b)) =
          S3134Step3115ThetaPilotReadout (I := I) D) :
    (-|Real.log (S3134QParameter J)|) ∈
      hullLogVolumeRay (S3134Step3115ThetaPilotReadout (I := I) D) := by
  have hbound :=
    S3134QThetaComparison_gap_comparison_ofMainlineRootedReadouts
      (I := I) (J := J) (T := T) (mu := mu) (D := D) hq hTheta
  have hle : (-|Real.log (S3134QParameter J)|) ≤
      S3134Step3115ThetaPilotReadout (I := I) D := by
    rw [S3134Step3115ThetaPilotReadout, S3134ThetaHullLogVolumeSigned]
    exact neg_le_neg hbound
  simpa only [hullLogVolumeRay, Set.mem_Iic] using hle

/-- The mainline q-side scalar bound `S3131QC T <= -|log Theta|` from the
mainline unconditional comparison plus the q-readout identification
`mainline q readout = S3131QC T` and the Theta readout identification. -/
theorem S3134Step3115_mainlineQC_le_thetaPilot_viaMainlineRooted
    (D : S1300HDDHullDetSource I)
    (hqc : (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * qPilotPaperLog (l := l) T b (mu b)) =
          S3131QC T)
    (hTheta : (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
            (mu b) (rootHalfCoefficient (l := l) T b)) =
          S3134Step3115ThetaPilotReadout (I := I) D) :
    S3131QC T ≤ S3134Step3115ThetaPilotReadout (I := I) D := by
  have h := S3134MainlineRooted_signedComparison (l := l) (T := T) mu
  rwa [hqc, hTheta] at h

/-! ## 2. Canonical paper-faithful rooted Q_C readout (no e=1 hypothesis)

Lead task-21 follow-up: the paper normalization is Q_p-spectral (c_norm = order/e;
IUT III Remark 3.1.1(ii), Prop. 3.9(i); IUT IV Prop. 1.4(i)).  The canonical
q-side readout is therefore the paper-faithful rooted spectral readout (weighted
`qPilotPaperLog` at `rootHalfCoefficient`), which IS the paper q-pilot readout by
construction; the old native `S3131QC` identification (default-residue norm) is
a separate optional e = 1 / F = Q identification, not a blocker. -/

/-- Canonical Q_C, consumed from mainline's landed declaration:
paper-faithful rooted spectral q-pilot readout.  By construction this IS the
paper q readout in the paper Q_p-spectral normalization; "-|log q|" is the paper
convention for it.  There is NO separate scalar theorem `QC = -|log q|`: the
explicit scalar value needs the registered per-b S778 identification
`PaperQPilotLogFormulaIdentification` (recorded below), which is not proved. -/
noncomputable abbrev S3134CanonicalRootedQC : ℝ :=
  S3131CanonicalRootedQC (l := l) T mu

/-- Canonical H_C, consumed from mainline's landed declaration: paper-faithful
rooted Theta-hull readout. -/
noncomputable abbrev S3134CanonicalRootedHC : ℝ :=
  S3131CanonicalRootedHC (l := l) T mu

/-- The canonical signed comparison is mainline's unconditional theorem. -/
theorem S3134CanonicalRootedQC_le_HC :
    S3134CanonicalRootedQC (l := l) T mu ≤
      S3134CanonicalRootedHC (l := l) T mu :=
  S3131CanonicalRootedQC_le_HC (l := l) T mu

/-- The q-half residual in explicit scalar form: the registered per-b S778
formula identification (`qPilotPaperLog_b = -(sum_i rootHalfCoefficient_i) *
log p_b`).  This is NOT proved in the tree; it is the exact gap between the
canonical (convention-defined) paper q readout and an explicit `-|log q|` scalar.
Recorded so that no numeric equality is claimed without it. -/
def S3134CanonicalRootedQFormulaGap : Prop :=
  forall b : Bad (nativePlaceSelection T),
    PaperQPilotLogFormulaIdentification (l := l) T b (mu b)

/-- If the registered S778 formula gap holds, the canonical Q_C readout has the
explicit scalar form.  This is the only honest numeric form of the q half. -/
theorem S3134CanonicalRootedQC_eq_scalar_of_formulaGap
    (h : S3134CanonicalRootedQFormulaGap (l := l) T mu) :
    S3134CanonicalRootedQC (l := l) T mu =
      -∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          ((∑ i, rootHalfCoefficient (l := l) T b i) *
            Real.log (qVFamTensorP T b : ℝ)) := by
  unfold S3134CanonicalRootedQC S3131CanonicalRootedQC
  calc
    (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * qPilotPaperLog (l := l) T b (mu b))
        = ∑ b : Bad (nativePlaceSelection T),
            nativeBadLocalWeight T b *
              (-((∑ i, rootHalfCoefficient (l := l) T b i) *
                Real.log (qVFamTensorP T b : ℝ))) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [h b]
    _ = -∑ b : Bad (nativePlaceSelection T),
          nativeBadLocalWeight T b *
            ((∑ i, rootHalfCoefficient (l := l) T b i) *
              Real.log (qVFamTensorP T b : ℝ)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro b _
          ring

/-- **Canonical consumer: the q residual is definitional.**  With the canonical
paper-faithful rooted Q_C readout, the only residual is the Theta-side readout
identification (canonical rooted H_C = the actual signed HDD Theta readout); no
q-side identification (and no e = 1 hypothesis) enters. -/
theorem S3134Step3115_canonicalQC_le_thetaPilot
    (D : S1300HDDHullDetSource I)
    (hH : S3134CanonicalRootedHC (l := l) T mu =
      S3134Step3115ThetaPilotReadout (I := I) D) :
    S3134CanonicalRootedQC (l := l) T mu ≤
      S3134Step3115ThetaPilotReadout (I := I) D := by
  rw [← hH]
  exact S3134CanonicalRootedQC_le_HC (l := l) T mu

/-- Canonical Step (xi-f) ray membership for the canonical paper q readout. -/
theorem S3134Step3115_canonicalQC_ray
    (D : S1300HDDHullDetSource I)
    (hH : S3134CanonicalRootedHC (l := l) T mu =
      S3134Step3115ThetaPilotReadout (I := I) D) :
    S3134CanonicalRootedQC (l := l) T mu ∈
      hullLogVolumeRay (S3134Step3115ThetaPilotReadout (I := I) D) := by
  have h :=
    S3134Step3115_canonicalQC_le_thetaPilot (l := l) (I := I) (T := T)
      (mu := mu) D hH
  simpa only [hullLogVolumeRay, Set.mem_Iic] using h

#check S3134MainlineRooted_signedComparison
#check S3134QThetaComparison_gap_comparison_ofMainlineRootedReadouts
#check S3134Step3115_ray_ofMainlineRootedReadouts
#check S3134Step3115_mainlineQC_le_thetaPilot_viaMainlineRooted
#check S3134CanonicalRootedQC
#check S3134CanonicalRootedHC
#check S3134CanonicalRootedQC_le_HC
#check S3134Step3115_canonicalQC_le_thetaPilot
#check S3134Step3115_canonicalQC_ray

end LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual
