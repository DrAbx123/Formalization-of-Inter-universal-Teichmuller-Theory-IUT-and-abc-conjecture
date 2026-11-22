import tmp.sheaf.xif.paper.S3134FourthJointQThetaActual

/-!
# S3134: determinant normalization of the actual Theta-side hull log-volume

IUT III, Corollary 3.12, Step (xi-d) (corpus `Inter-universal Teichmuller
Theory III.txt:10823-10864`) and Remark 3.9.5, (vii), (Ob1)--(Ob3-3)
(`:7875-8300`): after the holomorphic hull of the Theta-pilot image union is
formed, the `det (x) M` bookkeeping normalizes its log-volume: the normalized
log-volume of the determinant-tensor-power output is `M` times that of the
original arithmetic vector bundle.

The actual hull+det source `S1300HDDHullDetSource` carries exactly this
bookkeeping (`DetTensorPowerLogVolumeBookkeeping` with
`logVolume_detTensorPower`).  This file applies it to the actual Theta-side
hull region of the fourth triangle:

* `S3134ThetaHullDetLogVolume` is the det-normalized real log-volume of the
  actual hull region;
* `S3134ThetaHullDetLogVolume_eq_of_finite` proves it is the exponent times
  the actual hull log-volume (the only hypothesis is finiteness of the actual
  hull log-volume, which is itself a field of `S3134QThetaComparisonGap`);
* `S3134FourthJointComposite_snd_eq_transport_thetaRegion` proves that the
  actual hull region whose volume is normalized is exactly the region
  transported to the composite readout of the fourth joint.

No inequality is judged without constructed objects; no sorry, axiom, `True`,
`PUnit`, or toy carrier.  WRITE-ONLY: no lake/lean.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointCompositeActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual

namespace LeanFormal.IUT.XiFPaper.S3134ThetaHullDetNormalizationActual

universe u v uv ua upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The det-normalized real log-volume of the actual Theta-side hull region: the
`det (x) M` bookkeeping of the hull+det source applied to the actual hull
region of the fourth triangle. -/
noncomputable def S3134ThetaHullDetLogVolume
    (D : S1300HDDHullDetSource I) : ℝ :=
  (D.detData.logVolume
    (D.detData.detTensorPower (S3134ThetaHullRegion (I := I) D))).toReal

/-- The determinant normalization law of Step (xi-d)/(Ob3-3) on the actual
Theta-side readout: the det-normalized hull log-volume is the tensor-power
exponent times the actual hull log-volume.  The finiteness hypothesis is the
actual finiteness of the hull log-volume (a field of the comparison gap). -/
theorem S3134ThetaHullDetLogVolume_eq_of_finite
    (D : S1300HDDHullDetSource I)
    (hfin : D.detData.logVolume (S3134ThetaHullRegion (I := I) D) < ⊤) :
    S3134ThetaHullDetLogVolume (I := I) D =
      (D.detData.tensorPowerExponent : ℝ) * S3134ThetaHullLogVolume (I := I) D := by
  unfold S3134ThetaHullDetLogVolume
  rw [D.detData.logVolume_detTensorPower (S3134ThetaHullRegion (I := I) D)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  rw [S3134ThetaHullLogVolume_eq (I := I) D]

/-- Consumer of the comparison gap: under the gap's finiteness field the
det-normalization law applies to the actual Theta-side readout. -/
theorem S3134ThetaHullDetLogVolume_eq_of_gap
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D) :
    S3134ThetaHullDetLogVolume (I := I) D =
      (D.detData.tensorPowerExponent : ℝ) * S3134ThetaHullLogVolume (I := I) D :=
  S3134ThetaHullDetLogVolume_eq_of_finite (I := I) D
    G.theta_hull_log_volume_lt_top

/-- The actual Theta-side hull region whose log-volume enters the comparison is
exactly the region transported to the second component of the fourth-joint
composite arrow. -/
theorem S3134FourthJointComposite_snd_eq_transport_thetaRegion
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (v : NumberField.FinitePlace ℚ) :
    (S3134FourthJointComposite (I := I) (J := J) D C v).2 =
      (fun x : (i : Fin D.rank) → D.E i =>
        fun i => D.localEquiv v i (x i)) ''
      S3134ThetaHullRegion (I := I) D := by
  rw [S3134FourthJointComposite_snd,
    S3134HullDetReadout_eq_hull (I := I) D (S3134SHEOutputObject (I := I)) v]
  rfl

/-- The Theta-side target is the real part of the actual det-normalized
log-volume of the hull carried by the fourth-joint composite. -/
theorem S3134ThetaHullLogVolume_real_region
    (D : S1300HDDHullDetSource I) :
    S3134ThetaHullLogVolume (I := I) D =
      (D.detData.logVolume (S3134ThetaHullRegion (I := I) D)).toReal :=
  rfl

/-! ## The signed determinant normalization of the paper's `-|log(Theta)|` -/

/-- The signed determinant-normalized Theta-side target: the paper's
`-|log(Theta)|` after the `det (x) M` normalization. -/
noncomputable def S3134ThetaHullDetLogVolumeSigned
    (D : S1300HDDHullDetSource I) : ℝ :=
  - S3134ThetaHullDetLogVolume (I := I) D

/-- The determinant normalization law on the signed paper target: the signed
det-normalized hull log-volume is the tensor-power exponent times the signed
hull log-volume. -/
theorem S3134ThetaHullDetLogVolumeSigned_eq_of_gap
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D) :
    S3134ThetaHullDetLogVolumeSigned (I := I) D =
      (D.detData.tensorPowerExponent : ℝ) *
        S3134ThetaHullLogVolumeSigned (I := I) D := by
  unfold S3134ThetaHullDetLogVolumeSigned S3134ThetaHullLogVolumeSigned
  rw [S3134ThetaHullDetLogVolume_eq_of_gap (I := I) (J := J) D G]
  ring

#check S3134ThetaHullDetLogVolume
#check S3134ThetaHullDetLogVolume_eq_of_finite
#check S3134ThetaHullDetLogVolume_eq_of_gap
#check S3134ThetaHullDetLogVolumeSigned
#check S3134ThetaHullDetLogVolumeSigned_eq_of_gap
#check S3134FourthJointComposite_snd_eq_transport_thetaRegion

end LeanFormal.IUT.XiFPaper.S3134ThetaHullDetNormalizationActual
