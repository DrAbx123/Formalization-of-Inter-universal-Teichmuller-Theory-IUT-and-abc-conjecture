import tmp.sheaf.xif.SourceXiFConstruction
import tmp.sheaf.xif.paper.S1136SourceComparisonViaGluingActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceQSideComparison

/-!
# S1415: fixed-C marked trace, same readout, and the exact hull-readout field

This file follows route F of the 2026-10-30 gap report: for one fixed admissible
source datum C, expose a marked map/readout/monotone comparison using the
existing C9 trace and the S1136 conditional gluing skeleton.

The C9 trace fixes the q-pilot point at the source label j = 1 and asks for
a marked identification of that point with an allowed output, together with a
comparison read by the same source functional.  At the value layer of
SourceXiFConstruction this can be made actual without introducing a new
abstract carrier:

* the q mark is the actual q-pilot point sourceQPilotPoint (the theta-pilot
  point at the actual signed label 1);
* the allowed output source is the actual theta-pilot image set
  possibleThetaPilotImageSet;
* the same readout is the actual global log-degree sourceLocalLogDegree;
* the compatibility formula identifies the readout of every allowed image point
  with the source q-side normalized value at its label.

The q mark is proved to lie in the allowed output source and in the actual
holomorphic hull.  The paper-level cQ3/sQ3 marked map u_q,v, g_q, the
arithmetic-divisor/reference/weight identification, and the restricted
final-evaluation family membership are *not* constructed here; no free field or
Nonempty gate is added for them.  The exact first field left open at this
value layer is the boundedness of the actual hull readout image
(S1415HullReadoutFirstField).  From that field the S1136 gluing data and the
q/hull comparison are derived; the S1136 exact residual is proved equivalent to
the comparison itself.  This is not a scalar identity: the comparison comes from
membership of the actual q mark in the actual hull and from the supremum
definition of the hull readout.

Source correspondence: IUT III, Corollary 3.12, Step (xi), xi-d--xi-f; C9 trace
C9-U2K2-SQ3-MARKED-TRACE-20261026.md; S1136 monotone gluing skeleton.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1415MarkedTraceActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1136SourceComparisonViaGluingActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-! ## 1. The actual q mark -/

/-- The actual q mark at the value layer: the q-pilot point at the actual
signed label 1. -/
noncomputable def qMark : I.ThetaPilotPoint v :=
  I.sourceQPilotPoint v R n

theorem qMark_eq_sourceQPilotPoint :
    qMark I v R n = I.sourceQPilotPoint v R n := rfl

/-- The q mark is the realized standard q value, placed on every component of
the source value carrier. -/
theorem qMark_eq_constant_qValue :
    qMark I v R n =
      I.constantThetaPilotPoint v R
        (Multiplicative.ofAdd
          (Real.log ((I.theaterAt 0 0).thetaPacket.q))) := by
  unfold qMark sourceQPilotPoint
  rw [I.sourceThetaPilotPoint_eq_constant v R n (oneSignedLabel (l := l))]
  congr 1
  rw [I.log_thetaValueAt_eq_gauss n (oneSignedLabel (l := l)),
    oneSignedLabel_val, gaussExponent_one_toNat, Nat.cast_one, one_mul]

/-! ## 2. Allowed output source and its actual hull -/

/-- The allowed output source of the same fixed C: the actual theta-pilot
image set at the fixed procession. -/
noncomputable def allowedOutputSource : Set (I.ThetaPilotPoint v) :=
  I.possibleThetaPilotImageSet v R n

/-- The actual q mark lies in the allowed output source. -/
theorem qMark_mem_allowedOutputSource :
    qMark I v R n ∈ allowedOutputSource I v R n := by
  unfold qMark allowedOutputSource
  exact I.sourceThetaPilotPoint_mem v R n (oneSignedLabel (l := l))

/-- The actual holomorphic hull of the same source image. -/
noncomputable def hullSource : Set (I.ThetaPilotPoint v) :=
  (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))

/-- The allowed output source is contained in the actual hull. -/
theorem allowedOutputSource_subset_hull :
    allowedOutputSource I v R n ⊆ hullSource I v R n := by
  unfold allowedOutputSource hullSource
  exact I.possibleThetaPilotImage_subset_sourceHolomorphicHull v R n

/-- The q mark lies in the actual hull. -/
theorem qMark_mem_hull : qMark I v R n ∈ hullSource I v R n :=
  allowedOutputSource_subset_hull I v R n
    (qMark_mem_allowedOutputSource I v R n)

/-! ## 3. The same readout and its compatibility formula -/

/-- The same source readout on the q mark and on the allowed output points:
the actual global log-degree. -/
noncomputable def readout : I.ThetaPilotPoint v → Real :=
  I.sourceLocalLogDegree v

theorem readout_qMark :
    readout I v (qMark I v R n) = I.sourceQPilotLogVolume v R n := rfl

/-- Same-readout compatibility on each actual theta-pilot point: the global
source readout of the point is the q-side normalized value at its label. -/
theorem readout_sourceThetaPilotPoint_eq_sourceQSide
    (j : SignedLabel l.value) :
    readout I v (I.sourceThetaPilotPoint v R n j) =
      I.sourceQSideNormalizedValue n j := by
  unfold readout sourceQSideNormalizedValue
  rw [I.sourceLocalLogDegree_thetaPilotPoint_gauss v R n j,
    I.log_thetaValueAt_eq_gauss n j]

/-- Every actual allowed output point carries the same readout as its q-side
label. -/
theorem allowedOutputSource_readout_compat
    (x : I.ThetaPilotPoint v) (hx : x ∈ allowedOutputSource I v R n) :
    ∃ j : SignedLabel l.value,
      x = I.sourceThetaPilotPoint v R n j ∧
        readout I v x = I.sourceQSideNormalizedValue n j := by
  obtain ⟨j, rfl⟩ : ∃ j, x = I.sourceThetaPilotPoint v R n j :=
    (I.mem_possibleThetaPilotImageSet_iff v R n x).mp hx
  exact ⟨j, rfl, readout_sourceThetaPilotPoint_eq_sourceQSide I v R n j⟩

/-- The q-mark readout is card times the local q log-degree. -/
theorem readout_qMark_eq_card_mul_logDegree_q :
    readout I v (qMark I v R n) =
      (Fintype.card (SourceVolumeIndex l) : Real) *
        I.logDegreeAt 0 0 v
          (R.posRealAction (Multiplicative.ofAdd
            (Real.log ((I.theaterAt 0 0).thetaPacket.q)))) := by
  rw [qMark_eq_constant_qValue]
  unfold readout sourceLocalLogDegree
  simp only [I.constantThetaPilotPoint_apply]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The q-mark readout is card times the standard q-log. -/
theorem readout_qMark_eq_card_mul_log_q :
    readout I v (qMark I v R n) =
      (Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log ((I.theaterAt 0 0).thetaPacket.q) := by
  rw [readout_qMark_eq_card_mul_logDegree_q, R.degree_of_q]

/-- Same-readout compatibility at the q mark: its readout is the source q-side
normalized value at j = 1. -/
theorem readout_qMark_eq_sourceQSide :
    readout I v (qMark I v R n) =
      I.sourceQSideNormalizedValue n (oneSignedLabel (l := l)) := by
  rw [readout_qMark_eq_card_mul_log_q]
  unfold sourceQSideNormalizedValue
  rw [I.log_thetaValueAt_eq_gauss n (oneSignedLabel (l := l)),
    oneSignedLabel_val, gaussExponent_one_toNat, Nat.cast_one, one_mul]

/-! ## 4. The actual fixed-C marked trace -/

/-- The actual marked trace at the value layer: q mark, allowed output source,
actual hull, and the same-readout compatibility. -/
structure S1415MarkedTrace
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) where
  qMark : I.ThetaPilotPoint v
  outputSource : Set (I.ThetaPilotPoint v)
  hullSource : Set (I.ThetaPilotPoint v)
  qMark_mem_output : qMark ∈ outputSource
  output_subset_hull : outputSource ⊆ hullSource
  readout : I.ThetaPilotPoint v → Real
  qMark_readout_eq_qSide :
    readout qMark = I.sourceQSideNormalizedValue n (oneSignedLabel (l := l))

/-- The actual marked trace, constructed from the same fixed C. -/
noncomputable def actualMarkedTrace : S1415MarkedTrace I v R n where
  qMark := qMark I v R n
  outputSource := allowedOutputSource I v R n
  hullSource := hullSource I v R n
  qMark_mem_output := qMark_mem_allowedOutputSource I v R n
  output_subset_hull := allowedOutputSource_subset_hull I v R n
  readout := readout I v
  qMark_readout_eq_qSide := readout_qMark_eq_sourceQSide I v R n

@[simp] theorem actualMarkedTrace_qMark :
    (actualMarkedTrace I v R n).qMark = qMark I v R n := rfl

@[simp] theorem actualMarkedTrace_outputSource :
    (actualMarkedTrace I v R n).outputSource =
      allowedOutputSource I v R n := rfl

@[simp] theorem actualMarkedTrace_hullSource :
    (actualMarkedTrace I v R n).hullSource = hullSource I v R n := rfl

@[simp] theorem actualMarkedTrace_readout :
    (actualMarkedTrace I v R n).readout = readout I v := rfl

/-! ## 5. The exact first field and the S1136 comparison -/

/-- Exact first field for the value-layer S1136 comparison: the image of the
actual hull under the same readout is bounded above.  This is a property of the
actual hull readout image, not a scalar identity, and no inhabitant is supplied
without a source hypothesis. -/
abbrev S1415HullReadoutFirstField : Prop :=
  BddAbove (I.sourceThetaHullLogValueSet v R n)

/-- The S1136 gluing data at the actual q and hull readouts, from the exact first
field.  The gluing map is the identity because both marks live in the same
source value carrier; no new source arrow is introduced by this definition. -/
noncomputable def s1136DataOfFirstField
    (h : S1415HullReadoutFirstField I v R n) : S1136GluingData where
  thetaPilotLog := readout I v (qMark I v R n)
  thetaHullLog := I.sourceThetaHullLogVolume v R n
  qPilotLog := I.sourceQPilotLogVolume v R n
  hullLog := I.sourceThetaHullLogVolume v R n
  glue := id
  glue_mono := fun hxy => hxy
  qPilotLog_eq := (readout_qMark I v R n).symm
  hullLog_eq := rfl
  theta_le := I.sourceXiFInclusion_of_bounded v R n h

/-- The S1136 comparison from the exact first field. -/
theorem s1415Comparison_of_firstField
    (h : S1415HullReadoutFirstField I v R n) :
    I.sourceQPilotLogVolume v R n ≤ I.sourceThetaHullLogVolume v R n :=
  s1136Comparison (s1136DataOfFirstField I v R n h)

/-- Direct value-layer form of the comparison, not routed through the scalar
S1136 wrapper: it uses the actual hull membership of the q mark and the
supremum definition of the hull readout. -/
theorem s1415Comparison_of_firstField_direct
    (h : S1415HullReadoutFirstField I v R n) :
    I.sourceQPilotLogVolume v R n ≤ I.sourceThetaHullLogVolume v R n :=
  I.sourceXiFInclusion_of_bounded v R n h

/-- The S1136 wrapper and the direct source comparison have the same
conclusion; the wrapper does not replace the actual hull-membership proof. -/
theorem s1415Comparison_of_firstField_eq_direct
    (h : S1415HullReadoutFirstField I v R n) :
    s1415Comparison_of_firstField I v R n h =
      s1415Comparison_of_firstField_direct I v R n h := rfl

/-- The S1136 exact residual at the actual marked trace is exactly the q/hull
comparison. -/
theorem s1415ExactResidual_iff
    (h : S1415HullReadoutFirstField I v R n) :
    S1136ComparisonExactResidual (s1136DataOfFirstField I v R n h) ↔
      I.sourceQPilotLogVolume v R n ≤
        I.sourceThetaHullLogVolume v R n := by
  rfl

/-- The exact first field follows from the actual source q-contraction and the
scaling-unit contraction already named in the xi-f source construction. -/
theorem s1415HullReadoutFirstField_of_contracted
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    S1415HullReadoutFirstField I v R n :=
  I.sourceThetaHullLogValueSet_bddAbove_of_contracted v R n hq hScaling

/-- The q/hull comparison from the two actual source contraction conditions. -/
theorem s1415Comparison_of_contracted
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    I.sourceQPilotLogVolume v R n ≤ I.sourceThetaHullLogVolume v R n :=
  s1415Comparison_of_firstField I v R n
    (s1415HullReadoutFirstField_of_contracted I v R n hq hScaling)

#check qMark
#check qMark_eq_constant_qValue
#check qMark_mem_allowedOutputSource
#check qMark_mem_hull
#check readout_sourceThetaPilotPoint_eq_sourceQSide
#check allowedOutputSource_readout_compat
#check readout_qMark_eq_card_mul_logDegree_q
#check readout_qMark_eq_sourceQSide
#check actualMarkedTrace
#check s1415Comparison_of_firstField
#check s1415Comparison_of_firstField_direct
#check s1415Comparison_of_firstField_eq_direct
#check s1415ExactResidual_iff
#check s1415Comparison_of_contracted

end LeanFormal.IUT.XiFPaper.S1415MarkedTraceActual

end
