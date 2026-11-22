import tmp.sheaf.xif.paper.S3128Stage1FourthJointFullChainActual
import tmp.sheaf.xif.paper.S3134FourthJointTriangleActual
import tmp.sheaf.xif.paper.S3134ThetaHullDetNormalizationActual
import tmp.sheaf.xif.paper.S3134OneColumnPacketLogVolumeActual

/-!
# S3134: closed chain of the Stage 1 fourth joint

This file is the single consumer entry point of the fourth-joint stream: it
combines, in one theorem on actual objects,

1. the fixed fourth-joint chain of `S3128Stage1FourthJointFullChain`
   (FourthJoint premise, SHE composition premise, HDD rank, actual transported
   hull, frozen hull+det specification, determinant bookkeeping);
2. the composite arrow `(hull+det)∘(dsc)SHE` of
   `S3134FourthJointCompositeActual`, evaluated at the actual SHE output object
   (SHE unit-section readout, nonempty hull, and the identification of the hull
   region carried by the composite with the actual Theta-side hull region);
3. the determinant normalization law of `S3134ThetaHullDetNormalizationActual`
   on the paper's signed Theta-side target `-|log(Theta)|`;
4. the q/Theta simultaneous comparison card of
   `S3134FourthJointQThetaActual` (q-side `-|log(q)|`) and the actual
   procession average of the 1-column theta packet.

`S3134FourthJointClosedChain_final` then derives `C_Theta >= -1` from the same
data with the determinant-normalized linear comparison input.

The named comparison gap `S3134QThetaComparisonGap` remains the only non-actual
input (|log q| != 0, hull log-volume finiteness, Step (xi-f) comparison).  No
sorry, axiom, `True`, `PUnit`, or toy carrier.  WRITE-ONLY: no lake/lean.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128SHEHDDInterfaceActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionActual
open LeanFormal.IUT.XiFPaper.S3128Stage1FourthJointFullChainActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointCompositeActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual
open LeanFormal.IUT.XiFPaper.S3134ThetaHullDetNormalizationActual
open LeanFormal.IUT.XiFPaper.S3134OneColumnPacketLogVolumeActual

namespace LeanFormal.IUT.XiFPaper.S3134FourthJointClosedChainActual

universe u v uv ua upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Closed chain of the Stage 1 fourth joint on actual objects. -/
theorem S3134FourthJointClosedChain
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (G : S3134QThetaComparisonGap (I := I) (J := J) D)
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    S3128Stage1SHEHDDFourthJointPremise (I := I) (J := J) D
      ∧ S3128Stage1SHECompositionPremise (J := J)
      ∧ (D.toS1215 (I := I)).rank = D.rank
      ∧ (D.toS1215 (I := I)).lattice o v =
          (fun x : (i : Fin D.rank) → D.E i =>
            fun i => D.localEquiv v i (x i)) ''
          @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField (D.image o)
      ∧ (S3134FourthJointComposite (I := I) (J := J) D C v).1 =
          (actualSHEOutput I).bundle.localization v unitSection
      ∧ (S3134FourthJointComposite (I := I) (J := J) D C v).2.Nonempty
      ∧ (S3134FourthJointComposite (I := I) (J := J) D C v).2 =
          (fun x : (i : Fin D.rank) → D.E i =>
            fun i => D.localEquiv v i (x i)) ''
          S3134ThetaHullRegion (I := I) D
      ∧ S3134ThetaHullDetLogVolumeSigned (I := I) D =
          (D.detData.tensorPowerExponent : ℝ) *
            S3134ThetaHullLogVolumeSigned (I := I) D
      ∧ (S3134QThetaComparisonData (I := I) (J := J) D G).qPilotLogVolume =
          -|Real.log (S3134QParameter J)|
      ∧ S3134OneColumnAverageLogScale (J := J) =
          ((∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : ℝ)) /
            (Fintype.card (SignedLabel l.value) : ℝ)) *
            Real.log (S3134QParameter J) := by
  let F := S3128Stage1FourthJointFullChain (I := I) (J := J) D o v
  exact ⟨F.1, F.2.1, F.2.2.1, F.2.2.2.1,
    (S3134FourthJointComposite_fst (I := I) (J := J) D C v).trans
      (S3134SHEReadout_eq_actual (I := I) (J := J) C v
        (S3134SHEOutputObject (I := I))),
    S3134FourthJointComposite_snd_nonempty (I := I) (J := J) D C v,
    S3134FourthJointComposite_snd_eq_transport_thetaRegion (I := I) (J := J) D C v,
    S3134ThetaHullDetLogVolumeSigned_eq_of_gap (I := I) (J := J) D G,
    S3134QThetaComparisonData_qPilot (I := I) (J := J) D G,
    S3134OneColumnAverageLogScale_eq (J := J)⟩

/-- Final arithmetic step of Corollary 3.12 at the closed chain: given the
determinant-normalized linear comparison, conclude `C_Theta >= -1`. -/
theorem S3134FourthJointClosedChain_final
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (G : S3134QThetaComparisonGap (I := I) (J := J) D)
    {cTheta : ℝ}
    (hc : S3134ThetaHullDetLogVolumeSigned (I := I) D ≤
      (D.detData.tensorPowerExponent : ℝ) *
        (cTheta * |Real.log (S3134QParameter J)|)) :
    -1 ≤ cTheta := by
  have hM : (0 : ℝ) < (D.detData.tensorPowerExponent : ℝ) :=
    Nat.cast_pos.mpr D.detData.tensorPowerExponent_pos
  have hdet := S3134ThetaHullDetLogVolumeSigned_eq_of_gap (I := I) (J := J) D G
  have hmul : (D.detData.tensorPowerExponent : ℝ) *
        S3134ThetaHullLogVolumeSigned (I := I) D ≤
      (D.detData.tensorPowerExponent : ℝ) *
        (cTheta * |Real.log (S3134QParameter J)|) := by
    rw [← hdet]
    exact hc
  exact S3134QThetaComparison_final (I := I) (J := J) D G
    (le_of_mul_le_mul_left hmul hM)

#check S3134FourthJointClosedChain
#check S3134FourthJointClosedChain_final

end LeanFormal.IUT.XiFPaper.S3134FourthJointClosedChainActual
