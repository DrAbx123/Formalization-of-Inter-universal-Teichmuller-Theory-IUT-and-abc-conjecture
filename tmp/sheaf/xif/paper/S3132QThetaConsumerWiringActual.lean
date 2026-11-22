import tmp.sheaf.xif.paper.S3134FourthJointQThetaActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual
import tmp.sheaf.xif.paper.S3129IQHullLogVolumeSourceActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3132QThetaConsumerWiringActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual

universe u v uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I2 : OriginalInput.{0, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I2)

local instance qThetaWiringMeas : MeasurableSpace (C3LogShellTensorBlock C3) :=
  borel _

local instance qThetaWiringBorel : BorelSpace (C3LogShellTensorBlock C3) :=
  ⟨rfl⟩

/-!
# qTheta consumer wiring: exact Missing record + consumer theorems

**Component, not a paper object.**  Consumers: the fourth-triangle q/Theta
comparison (`S3134QThetaComparisonGap` / `Cor312ComparisonData`) and the
`S3130QCLeHCData` H_C handoff (mainline/lattice R1 residual).

The actual paper-hull Haar readout on the actual C3 log-shell tensor packet is
the expression `actualC3LogShellTensorHaar C3
(actualHolomorphicHull C3 (actualUnitRegion C3))`; it is finite because the
paper hull of the actual tensor region *is* the actual compact tensor region
(`actualHolomorphicHull_unitRegion_eq`, `actualC3LogShellTensorRegion_compact`;
the same readout object is packaged in
`S3132PaperHullSetPropertiesActual.paperHullHaarReadout`).

The remaining exact bridge between the Stage-1 fourth-joint hull+det readout of
`D` and this actual paper-hull readout is isolated field-level as
`MissingC3ThetaHullReadoutIdentification` (one equality of `ENNReal`
log-volume magnitudes); with it, the finiteness field of
`S3134QThetaComparisonGap` is discharged, and only the paper's `|log(q)| > 0`
and signed Step (xi-f) comparison remain as explicit hypotheses.

Sign caution (paper): IUT III Corollary 3.12 (corpus 10352-10353) asserts the
signed comparison `-|log(Theta)| >= -|log(q)|` (i.e. `H <= |log q|` in positive
magnitudes).  No comparison and no cross-carrier hull containment is asserted.

Source: IUT III, Remark 3.9.5, (i), (ii) (pp. 158-160); Proposition 3.9, (i)
(p. 115); Corollary 3.12 proof Steps (xi-d)-(xi-f) (pp. 174-175); IUT IV,
Theorem 1.10 (pp. 26-27).
-/

/-- **Exact missing bridge (field-level).**  The Stage-1 fourth-joint hull+det
Theta-side log-volume magnitude of `D` equals the actual C3-packet paper-hull
Haar readout.  No carrier identification is asserted and this equality is not
constructed. -/
structure MissingC3ThetaHullReadoutIdentification
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (I : Input Label Choice)
    {l : PrimeGeFive} {V : Type uv}
    {I2 : OriginalInput.{0, uv, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource I) : Prop where
  hull_logVolume_eq :
    D.detData.logVolume (S3134ThetaHullRegion (I := I) D) =
      actualC3LogShellTensorHaar C3
        (actualHolomorphicHull C3 (actualUnitRegion C3))

/-- **Finiteness of the Theta-side hull log-volume from the actual paper hull.** -/
theorem thetaHullLogVolume_lt_top_of_missing
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    {I : Input Label Choice}
    {l : PrimeGeFive} {V : Type uv}
    {I2 : OriginalInput.{0, uv, upi, umon, ui} l V}
    {C3 : SourcePilotRegionData (l := l) (V := V) I2}
    {D : S1300HDDHullDetSource I}
    (M : MissingC3ThetaHullReadoutIdentification I C3 D) :
    D.detData.logVolume (S3134ThetaHullRegion (I := I) D) < ⊤ := by
  rw [M.hull_logVolume_eq]
  rw [actualHolomorphicHull_unitRegion_eq C3]
  haveI hAdd : Measure.IsAddHaarMeasure (actualC3LogShellTensorHaar C3) :=
    inferInstance
  haveI hFin : IsFiniteMeasureOnCompacts (actualC3LogShellTensorHaar C3) :=
    hAdd.toIsFiniteMeasureOnCompacts
  exact (actualC3LogShellTensorRegion_compact C3).measure_lt_top

/-- **Consumer theorem: the q/Theta comparison gap from the actual paper hull.**
The missing bridge discharges the finiteness field; the two remaining fields are
the paper's own inputs (`|log(q)| > 0` and the signed Step (xi-f) comparison),
passed as explicit hypotheses. -/
theorem S3134QThetaComparisonGap_of_c3HullReadout
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (I : Input Label Choice)
    {l : PrimeGeFive} {V : Type uv}
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    {I2 : OriginalInput.{0, uv, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource I)
    (M : MissingC3ThetaHullReadoutIdentification I C3 D)
    (hq : Real.log (S3134QParameter J) ≠ 0)
    (hcmp : (-|Real.log (S3134QParameter J)|) ∈
      hullLogVolumeRay (S3134ThetaHullLogVolumeSigned (I := I) D)) :
    S3134QThetaComparisonGap (I := I) (J := J) D where
  q_log_ne_zero := hq
  theta_hull_log_volume_lt_top :=
    thetaHullLogVolume_lt_top_of_missing M
  simultaneous_comparison := hcmp

/-- **Final `C_Theta >= -1` step through the actual paper-hull readout.** -/
theorem S3134QThetaComparison_final_of_c3HullReadout
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (I : Input Label Choice)
    {l : PrimeGeFive} {V : Type uv}
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    {I2 : OriginalInput.{0, uv, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource I)
    (M : MissingC3ThetaHullReadoutIdentification I C3 D)
    (hq : Real.log (S3134QParameter J) ≠ 0)
    (hcmp : (-|Real.log (S3134QParameter J)|) ∈
      hullLogVolumeRay (S3134ThetaHullLogVolumeSigned (I := I) D))
    {cTheta : ℝ}
    (hc : S3134ThetaHullLogVolumeSigned (I := I) D ≤
      cTheta * |Real.log (S3134QParameter J)|) :
    -1 ≤ cTheta :=
  S3134QThetaComparison_final (I := I) (J := J) D
    (S3134QThetaComparisonGap_of_c3HullReadout I J C3 D M hq hcmp) hc

/-- **Named H_C input for the q/Theta comparison (S3130QCLeHCData shape).**  The
actual concrete-completion H_C hull log-volume is finite. -/
theorem sourceHullLogVolume_finite_namedInput :
    (LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual.sourceIQHullLogVolume).logVolume
        (LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual.sourceIQHullLogVolume).hull < ⊤ :=
  LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual.sourceIQHull_hull_logVolume_lt_top

#check MissingC3ThetaHullReadoutIdentification
#check thetaHullLogVolume_lt_top_of_missing
#check S3134QThetaComparisonGap_of_c3HullReadout
#check S3134QThetaComparison_final_of_c3HullReadout
#check sourceHullLogVolume_finite_namedInput

end LeanFormal.IUT.XiFPaper.S3132QThetaConsumerWiringActual

end
