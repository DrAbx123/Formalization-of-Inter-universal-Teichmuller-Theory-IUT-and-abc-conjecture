import tmp.sheaf.xif.paper.S3128Stage1FourthJointFullChainActual
import tmp.sheaf.xif.paper.S3134FourthJointCompositeActual
import tmp.sheaf.xif.paper.S3134FourthJointClosedChainActual
import tmp.sheaf.xif.paper.S3134FourthJointTriangleActual
import tmp.sheaf.xif.paper.S3134Step3115To312Actual
import tmp.sheaf.xif.paper.S3137NativeToC3SameCReadoutActual

/-!
# S3134: fourth-triangle composition status and wiring to the R1 same-C readout residual

**Component, not paper object.**  This file makes the fourth-triangle
composition explicit (IUT III, Corollary 3.12, corpus `III-T.txt:10324-10353`;
Step (xi-d) :10823-10864, Step (xi-e) :10864-10888, Step (xi-f) :10888-10899):
the fourth triangle is `(hull+det) o (dsc)SHE + IPL`, and it actually produces
the numerical q/Theta comparison from actual objects; it does not assume the
qualitative (xi-e) statement.

## Composition status

1st/2nd/3rd triangles (APT / theta-lattice / IPL links) are separate streams:
the IPL data consumed here is `actualIPLData (I := J)` with
`S3134FourthJointTriangle_ipl_inputLink_eq_composite` and the q-pilot strip
coherence `S3134FourthJointIPLQPilotStrip_coherence` (the strip and the q of
the `(1,0)` theater); no APT/IPL theorem is proved in this file.

4th triangle (actual):
* `S3134FourthJointComposite (D) (C) (v) =
    (S3134SHEReadout C v (S3134SHEOutputObject I),
     S3134HullDetReadout D (S3134SHEOutputObject I) v)` composes the SHE arrow at
  the actual SHE output object with the actual `S1300`/`S1385` hull+det arrow
  (`S3134FourthJointCompositeActual`);
* `S3128Stage1FourthJointFullChain` is the closed full chain (FourthJoint
  premise, SHE composition premise, HDD rank/hull/det, frozen spec,
  det tensor-power bookkeeping);
* the closed chain `S3134FourthJointClosedChain` adds the composite laws, the
  determinant-normalized signed volume identity and the actual q-pilot readout;
* the numerical readout produced is the pair
  `S3134Step3115QPilotReadout = -|log q|` and
  `S3134Step3115ThetaPilotReadout = S3134ThetaHullLogVolumeSigned = -|log Theta|`.
  The Step (xi-f) comparison itself is NOT produced by the qualitative data; it
  is the named residual `S3134Step3115Residual` /
  `S3134QThetaComparisonGap.simultaneous_comparison` (unless supplied by the
  mainline unconditional paper-faithful comparison, wired in
  `S3134MainlineRootedHFaActual`).

## R1 wiring

The `S3137NativeToC3SameCReadoutActual` residual
`NativeToC3SameCReadoutIdentification T mu C3 P` identifies the Stage-2 (C3, P)
readings with the mainline regional readouts.  Here its consequence
`qThetaMagnitudeComparison_of_nativeIdentification` is chained with the exact
named identification `S3134FourthTriangleToC3ReadoutIdentification` (actual
fourth-triangle signed readouts = Stage-2 signed readings) to yield the actual
fourth-triangle Step (xi-f) residual.  The latter identification is a
cross-carrier same-C model identification (my `S1300` HDD/SHE fourth-triangle
carrier vs R1's `SourcePilotRegionData` / `PaperQPilotObjectActual`); it is
recorded exactly, not constructed.

No sorry/axiom/arbitrary carrier; imported objects are the actual citable
S3134/S3128/S3137 objects.  WRITE-ONLY: no lake/lean.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

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
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137QThetaComparisonBridgeActual
open LeanFormal.IUT.XiFPaper.S3137NativeToC3SameCReadoutActual
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.S3134FourthTriangleCompositionStatusActual

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
variable {V0 : Type} {I0 : OriginalInput l V0}
variable (C3 : SourcePilotRegionData (l := l) (V := V0) I0)
variable (P : PaperQPilotObjectActual (l := l) (I := I0))

/-! ## 1. The 4th-triangle composite: hull+det after SHE -/

/-- The composite arrow `(hull+det) o (dsc)SHE` on actual objects: its SHE
component is the actual unit-section localization of the actual line bundle
(the `S1204` one-column readout), and its hull+det component is the actual
transported local-field hull of the `S1300`/`S1385` HDD image family at the
actual SHE output object. -/
theorem S3134FourthTriangle_hullDet_after_SHE
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (v : NumberField.FinitePlace ℚ) :
    (S3134FourthJointComposite (I := I) (J := J) D C v).1 =
        (actualSHEOutput I).bundle.localization v unitSection ∧
      (S3134FourthJointComposite (I := I) (J := J) D C v).2 =
        (fun x : (i : Fin D.rank) → D.E i =>
          fun i => D.localEquiv v i (x i)) ''
          @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField
            (D.image (S3134SHEOutputObject (I := I))) :=
  ⟨(S3134FourthJointComposite_fst (I := I) (J := J) D C v).trans
      (S3134SHEReadout_eq_actual (I := I) (J := J) C v
        (S3134SHEOutputObject (I := I))),
    (S3134FourthJointComposite_snd (I := I) (J := J) D C v).trans
      (S3134HullDetReadout_eq_hull (I := I) D
        (S3134SHEOutputObject (I := I)) v)⟩

/-- The closed chain's numerical readouts: the determinant-normalized signed
Theta log-volume identity, the actual q-pilot readout `-|log q|`, and the
composite hull component equal to the transport of the actual `S1300` hull. -/
theorem S3134FourthTriangle_closedChain_readouts
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (G : S3134QThetaComparisonGap (I := I) (J := J) D)
    (v : NumberField.FinitePlace ℚ) :
    S3134ThetaHullDetLogVolumeSigned (I := I) D =
        (D.detData.tensorPowerExponent : ℝ) *
          S3134ThetaHullLogVolumeSigned (I := I) D ∧
      (S3134QThetaComparisonData (I := I) (J := J) D G).qPilotLogVolume =
        -|Real.log (S3134QParameter J)| ∧
      (S3134FourthJointComposite (I := I) (J := J) D C v).2 =
        (fun x : (i : Fin D.rank) → D.E i =>
          fun i => D.localEquiv v i (x i)) ''
          S3134ThetaHullRegion (I := I) D :=
  ⟨S3134ThetaHullDetLogVolumeSigned_eq_of_gap (I := I) (J := J) D G,
    S3134QThetaComparisonData_qPilot (I := I) (J := J) D G,
    S3134FourthJointComposite_snd_eq_transport_thetaRegion
      (I := I) (J := J) D C v⟩

/-! ## 2. The 4th-triangle packet and its actual IPL slot -/

/-- The fourth-triangle packet's actual readouts and IPL coherence: q readout is
the actual `(1,0)`-column q, the Theta readout is the signed hull+det
log-volume `-|log Theta|`, and the IPL input link is the actual Kummer/evaluation
composite on the q-pilot strip. -/
theorem S3134FourthTriangle_packet_readouts
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    (S3134FourthJointTriangle_ofActuals (I := I) (J := J) D C).qParameter =
        S3134QParameter J ∧
      (S3134FourthJointTriangle_ofActuals (I := I) (J := J) D C).thetaHullLogVolume =
        S3134ThetaHullLogVolumeSigned (I := I) D ∧
      (S3134FourthJointTriangle_ofActuals (I := I) (J := J) D C).ipl.inputLink =
        (S3134FourthJointTriangle_ofActuals (I := I) (J := J) D C).ipl.composite :=
  ⟨S3134FourthJointTriangle_qParameter (I := I) (J := J) D C,
    S3134FourthJointTriangle_thetaHullLogVolume (I := I) (J := J) D C,
    S3134FourthJointTriangle_ipl_inputLink_eq_composite (I := I) (J := J) D C⟩

/-! ## 3. Wiring the 4th-triangle readout to the R1 same-C residual -/

/-- Exact named cross-carrier identification: the actual fourth-triangle signed
readouts are the Stage-2 `(C3, P)` signed readings of the R1 same-C residual.
The fourth-triangle carrier is the actual `S1300` HDD/SHE hull+det output; the
R1 carrier is the Stage-2 pilot-region/paper-q-pilot object.  The two are the
same fixed input C read out on both sides (IUT III, Definition 3.8, (i), p. 112;
Proposition 3.9, (i), p. 115; Corollary 3.12, corpus lines 10324-10353). -/
def S3134FourthTriangleToC3ReadoutIdentification
    (D : S1300HDDHullDetSource I)
    (C3 : SourcePilotRegionData (l := l) (V := V0) I0)
    (P : PaperQPilotObjectActual (l := l) (I := I0)) : Prop :=
  S3134Step3115ThetaPilotReadout (I := I) D = thetaPilotHullLogVolumeReal C3 ∧
    S3134Step3115QPilotReadout (J := J) = qPilotLogVolumeReading P

/-- **4th-triangle Step (xi-f) from the R1 residual.**  The R1 same-C
identification (C3/P readings = mainline regional readouts) plus the exact
cross-carrier readout identification above yields the actual fourth-triangle
signed comparison: the actual q-side readout lies in the ray
`R_{<= -|log Theta|}` of the actual hull+det readout.  No qualitative (xi-e)
input is used; both sides are actual readouts and the comparison is R1's
unconditional regional comparison. -/
theorem S3134FourthTriangleResidual_of_R1Identification
    (D : S1300HDDHullDetSource I)
    (B : NativeToC3SameCReadoutIdentification (l := l) T mu C3 P)
    (H : S3134FourthTriangleToC3ReadoutIdentification
      (I := I) (J := J) (I0 := I0) D C3 P) :
    S3134Step3115QPilotReadout (J := J) ∈
      hullLogVolumeRay (S3134Step3115ThetaPilotReadout (I := I) D) := by
  obtain ⟨hTheta, hQ⟩ := H
  have hCmp :=
    qThetaMagnitudeComparison_of_nativeIdentification (l := l) T mu C3 P B
  have hle : qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3 :=
    neg_le_neg_iff.mp hCmp
  rw [← hQ, ← hTheta] at hle
  simpa only [hullLogVolumeRay, Set.mem_Iic] using hle

#check S3134FourthTriangle_hullDet_after_SHE
#check S3134FourthTriangle_closedChain_readouts
#check S3134FourthTriangle_packet_readouts
#check S3134FourthTriangleToC3ReadoutIdentification
#check S3134FourthTriangleResidual_of_R1Identification

end LeanFormal.IUT.XiFPaper.S3134FourthTriangleCompositionStatusActual
