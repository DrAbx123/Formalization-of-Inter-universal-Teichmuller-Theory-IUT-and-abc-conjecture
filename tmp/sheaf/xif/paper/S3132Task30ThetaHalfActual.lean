import tmp.sheaf.xif.paper.S3134FourthTriangleCompositionStatusActual
import tmp.sheaf.xif.paper.S3132R1ThetaHalfBridgeActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128SHEHDDInterfaceActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionActual
open LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointFullChainActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointCompositeActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointClosedChainActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointTriangleActual
open LeanFormal.IUT.XiFPaper.S3134ThetaHullDetNormalizationActual
open LeanFormal.IUT.XiFPaper.S3134Step3115To312Actual
open LeanFormal.IUT.XiFPaper.S3134FourthTriangleCompositionStatusActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137QThetaComparisonBridgeActual
open LeanFormal.IUT.XiFPaper.S3137NativeToC3SameCReadoutActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.S3132Task30ThetaHalfActual

universe u v uv upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{0, uv, upi, umon, ui} l V)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
variable {V0 : Type} {I0 : OriginalInput l V0}
variable (C3 : SourcePilotRegionData (l := l) (V := V0) I0)
variable (P : PaperQPilotObjectActual (l := l) (I := I0))

/-!
# task-30: the Theta-half of the fourth triangle — exact missing and its reduction

**Component, not a paper object.**  Owner: hull.  Consumers: shehdd's
`S3134FourthTriangleCompositionStatusActual` (the `H` field of
`S3134FourthTriangleToC3ReadoutIdentification`), lattice's R1 residual, and the
mainline/lattice qTheta comparison.

**Actual objects used.**  The actual fourth-triangle signed Theta readout
`S3134Step3115ThetaPilotReadout (I := I) D` (= `S3134ThetaHullLogVolumeSigned`:
the negative of the actual hull+det log-volume magnitude at the actual SHE
output object, shehdd's composition file) and the actual C3-packet Theta reading
`thetaPilotHullLogVolumeReal C3` (= logarithm of the actual Haar measure of the
actual paper hull `actualHolomorphicHull C3 (actualUnitRegion C3)`; that hull is
the actual tensor log-shell region, and its Haar finiteness is proved in
`S3132R1ThetaHalfBridgeActual` with my `S3132` paper-hull files).

**What is NOT derivable today.**  The two objects live on different carriers:
the fourth-triangle carrier `D.detData.logVolume` on the transported HDD
product hull of `D`'s conditional factor fields, versus the C3 tensor-block Haar
on the actual C3 log-shell packet.  No theorem in the tree identifies the two
carriers (shehdd: none in the S3134 chain; the first field of
`S1385UniformLocalEquiv` — a uniform identification of every HDD factor field
with the 1-column fields — is itself an exact missing record).  Their
conventions also differ (signed hull+det log-volume magnitude vs logarithm of a
Haar measure with a chosen normalization), so the equality is exactly the
readout identification recorded below.

**Construction plan (owner: hull; recorded per brief §11).**
1. Construct the uniform field comparison `S1385UniformLocalEquiv` (component,
   requires the HDD factor fields `D.E i` and the C3 fibers; currently exact
   missing) and push `D.detData.logVolume` to the C3 log-shell packet.
2. Identify the transported HDD hull with `actualHolomorphicHull C3
   (actualUnitRegion C3)` (hull normalization; IUT III Prop 3.9(i) p.115;
   Remark 3.9.5(i) pp.158-159).
3. Match the det normalization: `S3134ThetaHullDetLogVolumeSigned` carries the
   tensor-power exponent; the C3 side is normalized on the unit reference
   (`sourceHullHaar_integralLogShell_eq_one` for the concrete completion,
   `c3TensorLatticeCompacts` for the C3 packet).  The e = 1 passage is task-13's
   `QVFamNormalizedNormCompatibility`.
Pages: IUT III Definition 3.8, (i), p. 112; Proposition 3.9, (i), p. 115;
Corollary 3.12, corpus lines 10324-10353; IUT IV, Theorem 1.10, pp. 26-27.

**Minimal exact missing** (owner: hull; consume as a named hypothesis):
the equality `S3134Step3115ThetaPilotReadout (I := I) D =
thetaPilotHullLogVolumeReal C3`.  The equivalent rooted form asked for by
shehdd (`thetaPilotHullLogVolumeReal C3 =
sum_b nativeBadLocalWeight T b * rootThetaHullLog ... rootHalfCoefficient ...`)
is the same identification after unfolding the actual rooted readout; it is
recorded in the docstring rather than as a second field.
-/

/-- **Minimal exact missing Theta-half readout.**  The actual fourth-triangle
signed Theta readout equals the actual C3-packet Theta reading. -/
structure MissingFourthTriangleThetaHalfReadout
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (I : Input Label Choice)
    {l : PrimeGeFive} {V0 : Type} {I0 : OriginalInput l V0}
    (C3 : SourcePilotRegionData (l := l) (V := V0) I0)
    (D : S1300HDDHullDetSource I) : Prop where
  theta_readout_eq :
    S3134Step3115ThetaPilotReadout (I := I) D = thetaPilotHullLogVolumeReal C3

/-- **Reduction:** the Theta half of shehdd's `H` is exactly the minimal exact
missing above; the Q half is separate (actual q readout identification). -/
theorem S3134FourthTriangleToC3ReadoutIdentification_of_missingThetaHalf
    (D : S1300HDDHullDetSource I)
    (M : MissingFourthTriangleThetaHalfReadout (I := I) (I0 := I0) C3 D)
    (hq : S3134Step3115QPilotReadout (J := J) = qPilotLogVolumeReading P) :
    S3134FourthTriangleToC3ReadoutIdentification
      (I := I) (J := J) (I0 := I0) D C3 P :=
  ⟨M.theta_readout_eq, hq⟩

/-- **Fourth-triangle Step (xi-f) residual from the minimal exact missing.** -/
theorem S3134FourthTriangleResidual_of_missingThetaHalf
    (D : S1300HDDHullDetSource I)
    (B : NativeToC3SameCReadoutIdentification (l := l) T mu C3 P)
    (M : MissingFourthTriangleThetaHalfReadout (I := I) (I0 := I0) C3 D)
    (hq : S3134Step3115QPilotReadout (J := J) = qPilotLogVolumeReading P) :
    S3134Step3115QPilotReadout (J := J) ∈
      hullLogVolumeRay (S3134Step3115ThetaPilotReadout (I := I) D) := by
  have hCmp :=
    qThetaMagnitudeComparison_of_nativeIdentification (l := l) T mu C3 P B
  have hle : qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3 :=
    neg_le_neg_iff.mp hCmp
  have hID := S3134FourthTriangleToC3ReadoutIdentification_of_missingThetaHalf
    I J C3 P D M hq
  obtain ⟨hTheta, hQ⟩ := hID
  rw [← hQ, ← hTheta] at hle
  simpa only [hullLogVolumeRay, Set.mem_Iic] using hle

#check MissingFourthTriangleThetaHalfReadout
#check S3134FourthTriangleToC3ReadoutIdentification_of_missingThetaHalf
#check S3134FourthTriangleResidual_of_missingThetaHalf

end LeanFormal.IUT.XiFPaper.S3132Task30ThetaHalfActual

end