import tmp.sheaf.xif.paper.S3134FourthJointCompositeActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-!
# S3134: the q/Theta simultaneous comparison of the fourth triangle

IUT III, Corollary 3.12 statement (corpus `Inter-universal Teichmuller
Theory III.txt:10325-10360`): for the q-pilot log-volume `-|log(q)|` and the
procession-normalized mono-analytic log-volume `-|log(Theta)|` of the
holomorphic hull of the Theta-pilot image union one has
`-|log(Theta)| >= -|log(q)|`. Step (xi-f) (`:10888-10899`) states the same
comparison as the membership `-|log(q)| in R_{<= -|log(Theta)|}`.

This file isolates the output arrow of the fourth triangle on actual objects:

* the q-side readout is the actual q-parameter of the actual 1-column theta
  packet (`S3134QParameter`), with positivity proved from
  `FiniteThetaPacket.q_pos` and invariance along the column proved from the
  actual theta-link transport;
* the Theta-side target is the paper's signed `-|log(Theta)|`, recorded as
  `S3134ThetaHullLogVolumeSigned`: the negative of the actual det-normalized
  log-volume readout `S3134ThetaHullLogVolume` of the actual HDD hull of the
  image family, read through the actual determinant bookkeeping of the hull+det
  source at the actual SHE output object (i.e. of the composite arrow of
  `S3134FourthJointCompositeActual`).  The repo's `ENNReal` log-volumes are
  nonnegative magnitudes; the paper's sign is kept explicitly.

The single missing paper input -- `|log(q)| > 0` for the actual q, finiteness
of the actual hull log-volume, and the comparison itself -- is recorded as the
exact structure `S3134QThetaComparisonGap` with its paper location. From it,
the paper's `Cor312ComparisonData` card is constructed unconditionally on the
actual objects, and the final arithmetic step `C_Theta >= -1` is derived with
the already-proved `Cor312ComparisonData.final_bound`. No inequality is judged
without constructed actual objects; no sorry, axiom, `True`, `PUnit`, or toy
carrier is used. WRITE-ONLY: no lake/lean.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointCompositeActual

namespace LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual

universe u v uv ua upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual q-parameter of the fourth triangle: the q of the actual 1-column
theta packet at the fixed column. -/
noncomputable def S3134QParameter : ℝ :=
  J.oneColumnQ 0

/-- The q-parameter is the q of the actual theta packet of the actual theater at
the `(1,0)` column, i.e. of the q-pilot strip stage. -/
theorem S3134QParameter_eq_theaterQ :
    S3134QParameter J = (J.theaterAt 1 0).thetaPacket.q :=
  rfl

/-- The actual q-parameter is positive (`FiniteThetaPacket.q_pos`). -/
theorem S3134QParameter_pos : 0 < S3134QParameter J :=
  (J.oneColumnPacket 0).q_pos

/-- The q-parameter is invariant along the column: it is the same actual q as
the q of the theta packet at every stage of the 1-column theta-link. -/
theorem S3134QParameter_transport (m : Int) :
    S3134QParameter J = J.oneColumnQ m :=
  J.oneColumnQ_transport 0 m

/-- The nonnegative Theta-side log-volume magnitude of the fourth triangle: the
real part of the actual determinant log-volume of the actual HDD hull of the
image family, evaluated at the actual SHE output object.  The repo's
log-volume convention is `ENNReal` (nonnegative magnitudes); the paper's
signed target `-|log(Theta)|` is recorded separately below and is NOT replaced
by this magnitude. -/
noncomputable def S3134ThetaHullLogVolume
    (D : S1300HDDHullDetSource I) : ℝ :=
  (D.detData.logVolume
    (@LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField
      (D.image (S3134SHEOutputObject (I := I))))).toReal

/-- The argument of the Theta-side determinant readout: the actual HDD hull of
the image family at the actual SHE output object. -/
noncomputable def S3134ThetaHullRegion
    (D : S1300HDDHullDetSource I) :
    Set ((i : Fin D.rank) → D.E i) :=
  @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField
    (D.image (S3134SHEOutputObject (I := I)))

/-- The Theta-side readout is the real part of the actual determinant
log-volume of the actual hull region. -/
theorem S3134ThetaHullLogVolume_eq (D : S1300HDDHullDetSource I) :
    S3134ThetaHullLogVolume (I := I) D =
      (D.detData.logVolume (S3134ThetaHullRegion (I := I) D)).toReal :=
  rfl

/-- The nonnegative log-volume magnitude is nonnegative. -/
theorem S3134ThetaHullLogVolume_nonneg (D : S1300HDDHullDetSource I) :
    0 ≤ S3134ThetaHullLogVolume (I := I) D :=
  ENNReal.toReal_nonneg

/-- The paper's signed Theta-side target `-|log(Theta)|`: the negative of the
actual nonnegative log-volume magnitude of the hull.  IUT III, Corollary 3.12
writes `-|log(Theta)|`; the sign is part of the target and must not be
dropped. -/
noncomputable def S3134ThetaHullLogVolumeSigned
    (D : S1300HDDHullDetSource I) : ℝ :=
  - S3134ThetaHullLogVolume (I := I) D

/-- The signed Theta-side target is nonpositive, as in the paper's
`-|log(Theta)|`. -/
theorem S3134ThetaHullLogVolumeSigned_nonpos (D : S1300HDDHullDetSource I) :
    S3134ThetaHullLogVolumeSigned (I := I) D ≤ 0 :=
  neg_nonpos.mpr (S3134ThetaHullLogVolume_nonneg (I := I) D)

/-- The signed target is the text-book signed hull log-volume. -/
theorem S3134ThetaHullLogVolumeSigned_eq (D : S1300HDDHullDetSource I) :
    S3134ThetaHullLogVolumeSigned (I := I) D =
      -(D.detData.logVolume (S3134ThetaHullRegion (I := I) D)).toReal :=
  rfl

/-- Exact remaining content of the fourth triangle: the simultaneous q/Theta
comparison for the actual q-parameter and the actual hull+det target.  The
three fields are exactly the paper's inputs that the present actual data do not
yet supply (`|log(q)| > 0` and the finiteness of the hull log-volume from the
compactness of `1, circ U`; the comparison of Step (xi-f)); they are recorded
as an exact structure with the paper location, not assumed silently. -/
structure S3134QThetaComparisonGap
    (D : S1300HDDHullDetSource I) : Prop where
  /-- `|log(q)| > 0` for the actual q-parameter of Corollary 3.12. -/
  q_log_ne_zero : Real.log (S3134QParameter J) ≠ 0
  /-- The actual hull log-volume is finite (`-|log(Theta)| in R`). -/
  theta_hull_log_volume_lt_top :
    D.detData.logVolume (S3134ThetaHullRegion (I := I) D) < ⊤
  /-- Step (xi-f): the actual q-side log-volume lies in
  `R_{<= -|log(Theta)|}`, with the signed paper target
  `S3134ThetaHullLogVolumeSigned`; this is a genuine comparison between two
  signed quantities, not the trivial bound against a nonnegative magnitude. -/
  simultaneous_comparison :
    (-|Real.log (S3134QParameter J)|) ∈
      hullLogVolumeRay (S3134ThetaHullLogVolumeSigned (I := I) D)

/-- Construction of the paper's `Cor312ComparisonData` card from the actual
q-parameter, the actual hull+det target, and exactly the missing comparison
input. -/
noncomputable def S3134QThetaComparisonData
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D) :
    Cor312ComparisonData where
  thetaHullLogVolume := S3134ThetaHullLogVolumeSigned (I := I) D
  qPilotLogVolume := -|Real.log (S3134QParameter J)|
  qPilot_mem_ray := G.simultaneous_comparison
  qParameter := S3134QParameter J
  qParameter_pos := S3134QParameter_pos J
  qParameter_log_ne_zero := G.q_log_ne_zero
  qPilotLogVolume_eq := rfl

/-- The q-side of the constructed comparison card is the actual
`-|log(q)|` of the actual q-parameter. -/
@[simp] theorem S3134QThetaComparisonData_qPilot
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D) :
    (S3134QThetaComparisonData (I := I) (J := J) D G).qPilotLogVolume =
      -|Real.log (S3134QParameter J)| :=
  rfl

/-- The Theta-side of the constructed comparison card is the paper's signed
hull+det log-volume readout. -/
@[simp] theorem S3134QThetaComparisonData_theta
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D) :
    (S3134QThetaComparisonData (I := I) (J := J) D G).thetaHullLogVolume =
      S3134ThetaHullLogVolumeSigned (I := I) D :=
  rfl

/-- The ray membership of Step (xi-f) restated for the actual fourth-triangle
readouts, with the signed paper target. -/
theorem S3134QThetaComparison_ray
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D) :
    (-|Real.log (S3134QParameter J)|) ∈
      hullLogVolumeRay (S3134ThetaHullLogVolumeSigned (I := I) D) :=
  G.simultaneous_comparison

/-- Step (xi-f) is a genuine comparison of two signed quantities: with the
paper's signed target it is equivalent to the nonnegative hull log-volume
magnitude being bounded by `|log(q)|`.  This is the substantive form of the
comparison; the nonnegative magnitude alone would make the inequality
vacuous. -/
theorem S3134QThetaComparison_ray_iff_magnitude
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D) :
    ((-|Real.log (S3134QParameter J)|) ∈
        hullLogVolumeRay (S3134ThetaHullLogVolumeSigned (I := I) D)) ↔
      S3134ThetaHullLogVolume (I := I) D ≤
        |Real.log (S3134QParameter J)| := by
  simp only [hullLogVolumeRay, Set.mem_Iic, S3134ThetaHullLogVolumeSigned]
  exact neg_le_neg_iff

/-- The sign trap, recorded so that consumers cannot silently replace the
signed target by the nonnegative magnitude: comparing the signed q-side value
directly with the nonnegative log-volume magnitude is automatic (it is the
trivial inequality `-|log(q)| <= 0 <= H`) and is NOT the paper's Step (xi-f).
Only the signed statement `S3134QThetaComparison_ray` (equivalently the
magnitude bound of `S3134QThetaComparison_ray_iff_magnitude`) is the comparison
of Corollary 3.12. -/
theorem S3134QThetaComparison_magnitude_trivial
    (D : S1300HDDHullDetSource I) :
    -|Real.log (S3134QParameter J)| ≤
      S3134ThetaHullLogVolume (I := I) D :=
  (neg_nonpos.mpr (abs_nonneg _)).trans
    (S3134ThetaHullLogVolume_nonneg (I := I) D)

/-- The final arithmetic step of Corollary 3.12 (Step (xi-f)) on the actual
fourth-triangle readouts: given the linear comparison of the signed actual
hull log-volume `-|log(Theta)|` with `C_Theta * |log(q)|`, conclude
`C_Theta >= -1`. -/
theorem S3134QThetaComparison_final
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D)
    {cTheta : ℝ}
    (hc : S3134ThetaHullLogVolumeSigned (I := I) D ≤
      cTheta * |Real.log (S3134QParameter J)|) :
    -1 ≤ cTheta :=
  Cor312ComparisonData.final_bound
    (S3134QThetaComparisonData (I := I) (J := J) D G) hc

#check S3134QParameter
#check S3134QParameter_pos
#check S3134QParameter_transport
#check S3134ThetaHullLogVolume
#check S3134ThetaHullLogVolumeSigned
#check S3134ThetaHullLogVolumeSigned_nonpos
#check S3134QThetaComparisonGap
#check S3134QThetaComparisonData
#check S3134QThetaComparison_final

end LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual
