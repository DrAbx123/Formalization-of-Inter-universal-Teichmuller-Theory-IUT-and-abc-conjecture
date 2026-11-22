import tmp.sheaf.xif.paper.S3134FourthJointTriangleActual
import tmp.sheaf.xif.paper.S3134ThetaHullDetNormalizationActual
import tmp.sheaf.xif.paper.S3131QCActualReadout

/-!
# S3134: the actual 3.11.5 => 3.12 step (q-pilot vs Theta-pilot simultaneous comparison)

IUT III, Corollary 3.12: statement (corpus `Inter-universal Teichmuller
Theory III.txt:10325-10360`); proof Steps (xi-d)--(xi-g) (`:10823-10907`),
Step (xi-f) = `:10888-10899` (`-|log(q)| in R_{<= -|log(Theta)|}`).  The
formalized "3.11.5" is the fourth triangle (hull+det) o (dsc)SHE + IPL; its
output is the simultaneous comparison of the q-pilot and Theta-pilot
log-volumes.

This file assembles that comparison as an actual theorem on the objects of the
fourth-joint stream:

* the q-pilot readout is the signed `-|log(q)|` of the actual 1-column
  q-parameter (`S3134Step3115QPilotReadout`);
* the Theta-pilot readout is the signed `-|log(Theta)|` of the actual HDD
  hull+det log-volume (`S3134Step3115ThetaPilotReadout`);
* the simultaneous comparison is the ray membership
  `-|log(q)| in R_{<= -|log(Theta)|}`, named as
  `S3134Step3115Residual` and proved equivalent to the genuine magnitude
  bound `H <= |log(q)|` (`S3134Step3115Residual_iff`);
* the paper's `Cor312ComparisonData` and the bound `C_Theta >= -1` are
  assembled from it (`S3134Step3115_comparisonData`, `S3134Step3115_CTheta`).

Coordination inputs (named, not proved):
* mainline Batch A q-side readout `S3131QC` (S3131QCActualReadout): the
  same-C identification `S3131QC T = -|log(q)|` is
  `S3134MainlineQCSameC`; under it `S3131QC T` is bounded by the assembled
  Theta-pilot readout (`S3134Step3115_mainlineQC_le_thetaPilot`);
* lattice positions `(n,m)` of the log-theta-lattice (IUT III, Definition
  1.4; same `OriginalInput.linkAt_q` used by S3137*): the actual q readout is
  position-invariant (`S3134Step3115_latticeQInvariance`,
  `S3134Step3115_latticeSquare_q`).

The only residual of the step is exactly `S3134QThetaComparisonGap`
(|log q| != 0, hull log-volume finiteness, and the Step (xi-f) comparison);
it is reported, not assumed silently.  No sorry, axiom, `True`, `PUnit`, or
toy carrier.  WRITE-ONLY: no lake/lean.
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
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3131QCActualReadout
open LeanFormal.IUT.XiFPaper.S3134FourthJointCompositeActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointTriangleActual
open LeanFormal.IUT.XiFPaper.S3134ThetaHullDetNormalizationActual

namespace LeanFormal.IUT.XiFPaper.S3134Step3115To312Actual

universe u v uv ua upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. The named same-C coordination input -/

/-- Exact same-C coordination between the mainline Batch A q-side readout
`Q_C` and the actual q-pilot log-volume `-|log(q)|` of the fourth triangle.
Paper source: IUT III, Corollary 3.12 statement (`:10325-10360`) fixes
`-|log(q)|` as the q-pilot log-volume; Step (xi-f) (`:10888-10899`) places it
in `R_{<= -|log(Theta)|}`.  This is a named source identification between the
two actual readouts, not a consequence of their records. -/
def S3134MainlineQCSameC : Prop :=
  S3131QC T = -|Real.log (S3134QParameter J)|

/-- Projection of the named same-C identification. -/
theorem S3134MainlineQCSameC_eq
    (hid : S3134MainlineQCSameC (J := J) (T := T)) :
    S3131QC T = -|Real.log (S3134QParameter J)| :=
  hid

/-! ## 2. The two actual pilot readouts and the named residual -/

/-- Actual q-pilot readout of the fourth triangle: the signed q-parameter
log-volume `-|log(q)|`. -/
noncomputable def S3134Step3115QPilotReadout : ℝ :=
  -|Real.log (S3134QParameter J)|

/-- Actual Theta-pilot readout of the fourth triangle: the signed hull
log-volume `-|log(Theta)|` from the actual hull+det source. -/
noncomputable def S3134Step3115ThetaPilotReadout
    (D : S1300HDDHullDetSource I) : ℝ :=
  S3134ThetaHullLogVolumeSigned (I := I) D

/-- The named residual of the 3.11.5 => 3.12 step: the simultaneous comparison
`-|log(q)| in R_{<= -|log(Theta)|}` of Step (xi-f) (`:10888-10899`). -/
def S3134Step3115Residual
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D) : Prop :=
  S3134Step3115QPilotReadout (J := J) ∈
    hullLogVolumeRay (S3134Step3115ThetaPilotReadout (I := I) D)

/-- The named residual holds: it is exactly the simultaneous-comparison field
of the fourth-triangle comparison gap. -/
theorem S3134Step3115_residual_holds
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D) :
    S3134Step3115Residual (I := I) (J := J) D G := by
  simpa only [S3134Step3115Residual, S3134Step3115QPilotReadout,
    S3134Step3115ThetaPilotReadout] using G.simultaneous_comparison

/-! ## 3. The assembled simultaneous comparison -/

/-- The simultaneous comparison in ray-membership form. -/
theorem S3134Step3115_simultaneousComparison
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D) :
    S3134Step3115QPilotReadout (J := J) ∈
      hullLogVolumeRay (S3134Step3115ThetaPilotReadout (I := I) D) :=
  S3134Step3115_residual_holds (I := I) (J := J) D G

/-- The assembled comparison in the ordered form
`-|log(q)| <= -|log(Theta)|`. -/
theorem S3134Step3115_qPilot_le_thetaPilot
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D) :
    S3134Step3115QPilotReadout (J := J) ≤
      S3134Step3115ThetaPilotReadout (I := I) D := by
  simpa only [hullLogVolumeRay, Set.mem_Iic] using
    S3134Step3115_simultaneousComparison (I := I) (J := J) D G

/-- The assembled comparison in the genuine magnitude form of Corollary 3.12:
the actual hull log-volume magnitude is at most `|log(q)|`. -/
theorem S3134Step3115_magnitudeBound
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D) :
    S3134ThetaHullLogVolume (I := I) D ≤ |Real.log (S3134QParameter J)| :=
  (S3134QThetaComparison_ray_iff_magnitude (I := I) (J := J) D G).mp
    G.simultaneous_comparison

/-- The named residual is exactly the magnitude bound of Step (xi-f). -/
theorem S3134Step3115Residual_iff
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D) :
    S3134Step3115Residual (I := I) (J := J) D G ↔
      S3134ThetaHullLogVolume (I := I) D ≤ |Real.log (S3134QParameter J)| := by
  unfold S3134Step3115Residual S3134Step3115QPilotReadout
    S3134Step3115ThetaPilotReadout
  exact S3134QThetaComparison_ray_iff_magnitude (I := I) (J := J) D G

/-! ## 4. The assembled 3.11.5 => 3.12 conclusion -/

/-- The paper's comparison data card assembled from the fourth-joint packet. -/
noncomputable def S3134Step3115_comparisonData
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D) :
    Cor312ComparisonData :=
  S3134QThetaComparisonData (I := I) (J := J) D G

/-- 3.11.5 => 3.12, arithmetic form: `C_Theta >= -1` from the assembled
simultaneous comparison and the linear comparison state. -/
theorem S3134Step3115_CTheta
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D)
    {cTheta : ℝ}
    (hc : S3134Step3115ThetaPilotReadout (I := I) D ≤
      cTheta * |Real.log (S3134QParameter J)|) :
    -1 ≤ cTheta := by
  refine S3134QThetaComparison_final (I := I) (J := J) D G ?_
  simpa only [S3134Step3115ThetaPilotReadout] using hc

/-! ## 5. Mainline coordination: Q_C bounded by the assembled Theta target -/

/-- Consumer for the Batch A mainline: under the named same-C identification,
the mainline actual q-side readout `S3131QC T` is bounded by the fourth
triangle's assembled Theta-pilot readout. -/
theorem S3134Step3115_mainlineQC_le_thetaPilot
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D)
    (hid : S3134MainlineQCSameC (J := J) (T := T)) :
    S3131QC T ≤ S3134Step3115ThetaPilotReadout (I := I) D := by
  have h := S3134Step3115_qPilot_le_thetaPilot (I := I) (J := J) D G
  unfold S3134MainlineQCSameC at hid
  rw [hid]
  simpa only [S3134Step3115QPilotReadout] using h

/-! ## 6. Lattice coordination: q-pilot position invariance -/

/-- The actual q-pilot parameter is invariant under the log-theta-lattice
position: for every node `(n,m)` of the `[LGP-Gaussian]` log-theta-lattice
(IUT III, Definition 1.4), the theta packet of the actual theater at `(n,m)`
carries the same actual q.  This is the actual `linkAt_q` invariance, the same
source law used by S3137* for the lattice square. -/
theorem S3134Step3115_latticeQInvariance (n m : Int) :
    S3134QParameter J = (J.theaterAt n m).thetaPacket.q :=
  (S3134QParameter_eq_theaterQ (J := J)).trans (J.linkAt_q 1 0 n m)

/-- The lattice-square q invariance (Remark 1.4.1, (i)); this is the same
statement as `S3137LogThetaLatticeSquareActual.square_q_diagonal`, recorded
here for the fourth-triangle assembly. -/
theorem S3134Step3115_latticeSquare_q (n m : Int) :
    (J.theaterAt n m).thetaPacket.q =
      (J.theaterAt (n + 1) (m + 1)).thetaPacket.q :=
  J.linkAt_q n m (n + 1) (m + 1)

#check S3134MainlineQCSameC
#check S3134Step3115QPilotReadout
#check S3134Step3115ThetaPilotReadout
#check S3134Step3115Residual
#check S3134Step3115_simultaneousComparison
#check S3134Step3115_qPilot_le_thetaPilot
#check S3134Step3115_magnitudeBound
#check S3134Step3115Residual_iff
#check S3134Step3115_comparisonData
#check S3134Step3115_CTheta
#check S3134Step3115_mainlineQC_le_thetaPilot
#check S3134Step3115_latticeQInvariance

end LeanFormal.IUT.XiFPaper.S3134Step3115To312Actual
