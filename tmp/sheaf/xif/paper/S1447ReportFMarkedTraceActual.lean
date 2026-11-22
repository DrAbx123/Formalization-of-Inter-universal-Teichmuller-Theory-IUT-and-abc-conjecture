/-
# S1447: Route F marked trace and same readout

Fix one source input C.  This file formalises the C9 trace cancellation, the
actual value-layer q mark and theta-pilot source, the same-readout formula,
the monotone hull comparison, and the S1136 conditional skeleton.  The
paper-level final-evaluation output projection is recorded as an exact named
residual, not constructed and not assumed.

The value-layer comparison is genuine for the value layer.  It is not claimed
to be the paper IQ/O final-evaluation gate.
-/

import tmp.sheaf.xif.SourceXiFConstruction
import tmp.sheaf.xif.paper.S1136SourceComparisonViaGluingActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceQSideComparison
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1447MarkedTraceActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1136SourceComparisonViaGluingActual

universe ua uv upi umon ui uA uB

/-! ## 1. The C9 trace's U2 K2 cancellation -/

/-- The two-square part of the C9 marked trace.  L0,L1 are the lower
horizontals, K0,K1,K2 the verticals, and U0,U1,U2 the upper horizontals,
with the trace's right-to-left convention. -/
def c9IplComposite {A0 A1 A2 : Type uA} {B0 B1 B2 B3 : Type uB}
    (L0 : A0 ≃ A1) (L1 : A1 ≃ A2)
    (K0 : A0 → B0) (K1 : A1 → B1) (K2 : A2 → B2)
    (U0 : B0 → B1) (U1 : B1 → B2) (U2 : B2 → B3)
    (x : A2) : B3 :=
  U2 (U1 (U0 (K0 (L0.symm (L1.symm x)))))

/-- The marked map of the C9 trace: U2 K2. -/
def c9MarkedMap {A2 : Type uA} {B2 B3 : Type uB}
    (K2 : A2 → B2) (U2 : B2 → B3) (x : A2) : B3 :=
  U2 (K2 x)

/-- The C9 trace cancellation: the IPL composite
U2 U1 U0 K0 L0^-1 L1^-1 equals the marked map U2 K2, using the two
commuting squares. -/
theorem c9IplComposite_eq_markedMap {A0 A1 A2 : Type uA} {B0 B1 B2 B3 : Type uB}
    (L0 : A0 ≃ A1) (L1 : A1 ≃ A2)
    (K0 : A0 → B0) (K1 : A1 → B1) (K2 : A2 → B2)
    (U0 : B0 → B1) (U1 : B1 → B2) (U2 : B2 → B3)
    (h0 : ∀ a, U0 (K0 a) = K1 (L0 a))
    (h1 : ∀ a, U1 (K1 a) = K2 (L1 a))
    (x : A2) :
    c9IplComposite L0 L1 K0 K1 K2 U0 U1 U2 x =
      c9MarkedMap K2 U2 x := by
  unfold c9IplComposite c9MarkedMap
  rw [h0 (L0.symm (L1.symm x))]
  simp only [Equiv.apply_symm_apply]
  rw [h1 (L1.symm x)]
  simp only [Equiv.apply_symm_apply]

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- The actual q mark at the value layer. -/
noncomputable def qMark : I.ThetaPilotPoint v :=
  I.sourceQPilotPoint v R n

theorem qMark_eq_sourceQPilotPoint :
    qMark I v R n = I.sourceQPilotPoint v R n := rfl

/-- The actual q mark is the realized q value, placed on every component. -/
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

/-- The allowed output source: the actual theta-pilot image set. -/
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

/-- The same source readout on the q mark and the allowed output points. -/
noncomputable def readout : I.ThetaPilotPoint v → Real :=
  I.sourceLocalLogDegree v

theorem readout_qMark :
    readout I v (qMark I v R n) = I.sourceQPilotLogVolume v R n := rfl

theorem readout_qMark_mem_hullLogValueSet :
    readout I v (qMark I v R n) ∈ I.sourceThetaHullLogValueSet v R n :=
  ⟨qMark I v R n, qMark_mem_hull I v R n, rfl⟩

/-- Actual monotone comparison: the q-mark readout is at most the hull
log-volume, because the q mark lies in the hull and the hull log-volume is
the supremum of the same readout over the hull. -/
theorem readout_qMark_le_hullLog_of_bdd
    (hBdd : BddAbove (I.sourceThetaHullLogValueSet v R n)) :
    readout I v (qMark I v R n) ≤ I.sourceThetaHullLogVolume v R n :=
  le_csSup hBdd (readout_qMark_mem_hullLogValueSet I v R n)

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


/-- Same-readout compatibility on each actual theta-pilot point: the global
source readout of the point is the q-side normalized value at its label. -/
theorem readout_sourceThetaPilotPoint_eq_sourceQSide
    (j : SignedLabel l.value) :
    readout I v (I.sourceThetaPilotPoint v R n j) =
      I.sourceQSideNormalizedValue n j := by
  unfold readout sourceQSideNormalizedValue
  rw [I.sourceLocalLogDegree_thetaPilotPoint_gauss v R n j,
    I.log_thetaValueAt_eq_gauss n j]
/-- Same-readout compatibility: the q-mark readout is the source q-side value at j=1. -/
theorem readout_qMark_eq_sourceQSide :
    readout I v (qMark I v R n) =
      I.sourceQSideNormalizedValue n (oneSignedLabel (l := l)) := by
  rw [readout_qMark_eq_card_mul_log_q]
  unfold sourceQSideNormalizedValue
  rw [I.log_thetaValueAt_eq_gauss n (oneSignedLabel (l := l)),
    oneSignedLabel_val, gaussExponent_one_toNat, Nat.cast_one, one_mul]

/-- The actual fixed-C marked trace at the value layer. -/
structure S1447MarkedTrace
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) where
  qMark : I.ThetaPilotPoint v
  outputSource : Set (I.ThetaPilotPoint v)
  hullSource : Set (I.ThetaPilotPoint v)
  qMark_mem_output : qMark ∈ outputSource
  output_subset_hull : outputSource ⊆ hullSource
  readout : I.ThetaPilotPoint v → Real
  readout_qMark_eq_qSide :
    readout qMark = I.sourceQSideNormalizedValue n (oneSignedLabel (l := l))

/-- The actual marked trace, constructed from the same fixed C. -/
noncomputable def actualMarkedTrace : S1447MarkedTrace I v R n where
  qMark := qMark I v R n
  outputSource := allowedOutputSource I v R n
  hullSource := hullSource I v R n
  qMark_mem_output := qMark_mem_allowedOutputSource I v R n
  output_subset_hull := allowedOutputSource_subset_hull I v R n
  readout := readout I v
  readout_qMark_eq_qSide := readout_qMark_eq_sourceQSide I v R n

/-- Exact first field for the value-layer S1136 comparison: the image of the actual
hull under the same readout is bounded above. -/
abbrev S1447HullReadoutFirstField : Prop :=
  BddAbove (I.sourceThetaHullLogValueSet v R n)

/-- The S1136 gluing data at the actual q and hull readouts, from the exact first field. -/
noncomputable def s1136DataOfMarkedTrace
    (h : S1447HullReadoutFirstField I v R n) : S1136GluingData where
  thetaPilotLog := readout I v (qMark I v R n)
  thetaHullLog := I.sourceThetaHullLogVolume v R n
  qPilotLog := I.sourceQPilotLogVolume v R n
  hullLog := I.sourceThetaHullLogVolume v R n
  glue := id
  glue_mono := fun hxy => hxy
  qPilotLog_eq := (readout_qMark I v R n).symm
  hullLog_eq := rfl
  theta_le := readout_qMark_le_hullLog_of_bdd I v R n h

/-- The S1136 comparison from the exact first field. -/
theorem s1447Comparison_of_bdd
    (h : S1447HullReadoutFirstField I v R n) :
    I.sourceQPilotLogVolume v R n ≤ I.sourceThetaHullLogVolume v R n :=
  s1136Comparison (s1136DataOfMarkedTrace I v R n h)

/-- The S1136 exact residual at the actual marked trace is exactly the q/hull comparison. -/
theorem s1447ExactResidual_iff
    (h : S1447HullReadoutFirstField I v R n) :
    S1136ComparisonExactResidual (s1136DataOfMarkedTrace I v R n h) ↔
      I.sourceQPilotLogVolume v R n ≤ I.sourceThetaHullLogVolume v R n := by
  rfl

/-- The exact first field follows from the actual source q-contraction and the
scaling-unit contraction already named in the xi-f source construction. -/
theorem s1447HullReadoutFirstField_of_contracted
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    S1447HullReadoutFirstField I v R n :=
  I.sourceThetaHullLogValueSet_bddAbove_of_contracted v R n hq hScaling

/-- The q/hull comparison from the two actual source contraction conditions. -/
theorem s1447Comparison_of_contracted
    (hq : (I.theaterAt 0 0).thetaPacket.q ≤ 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    I.sourceQPilotLogVolume v R n ≤ I.sourceThetaHullLogVolume v R n :=
  s1447Comparison_of_bdd I v R n
    (s1447HullReadoutFirstField_of_contracted I v R n hq hScaling)

/-- Exact value-layer output witness: the q mark itself is a member of the
value-layer allowed source and its readout is exactly Q. -/
theorem valueLayerExactOutputWitness :
    ∃ D ∈ allowedOutputSource I v R n,
      readout I v D = I.sourceQPilotLogVolume v R n :=
  ⟨qMark I v R n, qMark_mem_allowedOutputSource I v R n, rfl⟩

/-- The same comparison via the exact output witness and the output hull bound,
without passing through the S1136 record. -/
theorem s1447Comparison_of_valueLayerExactWitness
    (hBdd : BddAbove (I.sourceThetaHullLogValueSet v R n)) :
    I.sourceQPilotLogVolume v R n ≤ I.sourceThetaHullLogVolume v R n := by
  obtain ⟨D, hD, hDread⟩ := valueLayerExactOutputWitness I v R n
  have hmem : readout I v D ∈ I.sourceThetaHullLogValueSet v R n :=
    ⟨D, allowedOutputSource_subset_hull I v R n hD, rfl⟩
  have hDle : readout I v D ≤ I.sourceThetaHullLogVolume v R n :=
    le_csSup hBdd hmem
  calc
    I.sourceQPilotLogVolume v R n = readout I v D := hDread.symm
    _ ≤ I.sourceThetaHullLogVolume v R n := hDle

/-! ## 3b. C9 marked transport across the fixed-C procession family -/

/-- The q mark read at another theater of the same fixed input. -/
noncomputable def qMarkAt (p : Int × Int) : I.ThetaPilotPoint v :=
  I.constantThetaPilotPoint v R
    (Multiplicative.ofAdd
      (Real.log ((I.theaterAt p.1 p.2).thetaPacket.q)))

/-- The q parameter is invariant under the source theater links, so the q mark
read at (0,0) is the q mark read at any other theater of the same C. -/
theorem qMarkAt_eq (p q : Int × Int) :
    qMarkAt I v R p = qMarkAt I v R q := by
  unfold qMarkAt
  rw [I.linkAt_q p.1 p.2 q.1 q.2]

theorem qMark_eq_qMarkAt_zero :
    qMark I v R n = qMarkAt I v R (0, 0) := by
  rw [qMark_eq_constant_qValue]
  rfl

theorem qMarkAt_zero_eq_horizontal :
    qMarkAt I v R (0, 0) = qMarkAt I v R (1, 0) :=
  qMarkAt_eq I v R (0, 0) (1, 0)

/-- The C9-style transport preserves the same readout: every theater's q mark
has the fixed q-pilot readout of the same C. -/
theorem readout_qMarkAt_eq (p : Int × Int) :
    readout I v (qMarkAt I v R p) = I.sourceQPilotLogVolume v R n := by
  have h : qMarkAt I v R p = qMark I v R n := by
    rw [qMarkAt_eq I v R p (0, 0), ← qMark_eq_qMarkAt_zero I v R n]
  rw [h, readout_qMark]

/-! ## 4. The exact paper-level residual and its consumer -/

/-- Exact output-readout coverage of a fixed value Q by a candidate actual
output family P with readout nu. -/
def S1447ExactCoverage {A : Type*} (P : Set A) (nu : A → Real) (Q : Real) : Prop :=
  ∃ D ∈ P, nu D = Q

/-- Signed-epsilon output-readout coverage, the paper's approximation form. -/
def S1447SignedCoverage {A : Type*} (P : Set A) (nu : A → Real) (Q : Real) : Prop :=
  ∀ eps : Real, 0 < eps → ∃ D ∈ P, Q - eps ≤ nu D

/-- The exact/signed output-readout projection: this is the paper-level
source arrow XiEToXiFOutputReadoutProjection(C).  It is a proposition, not
an axiom or a structure with a proof field. -/
def S1447OutputReadoutProjection {A : Type*}
    (P : Set A) (nu : A → Real) (Q : Real) : Prop :=
  S1447ExactCoverage P nu Q ∨ S1447SignedCoverage P nu Q

/-- The paper-level residual for the actual final-evaluation family.  P and nu
stand for the actual P_C and nu_C; the current source interface does not
construct them, so this remains an explicit parameter. -/
def S1447PaperOutputReadoutProjection {A : Type*}
    (P : Set A) (nu : A → Real) : Prop :=
  S1447OutputReadoutProjection P nu (I.sourceQPilotLogVolume v R n)

/-- Exact coverage plus the output hull bound gives the comparison. -/
theorem s1447Comparison_of_exactCoverage
    {A : Type*} {P : Set A} {nu : A → Real} {Q h : Real}
    (hbound : ∀ D ∈ P, nu D ≤ h)
    (hcover : S1447ExactCoverage P nu Q) : Q ≤ h := by
  obtain ⟨D, hD, hDQ⟩ := hcover
  calc
    Q = nu D := hDQ.symm
    _ ≤ h := hbound D hD

/-- Signed-epsilon coverage plus the output hull bound gives the comparison by
the midpoint argument. -/
theorem s1447Comparison_of_signedCoverage
    {A : Type*} {P : Set A} {nu : A → Real} {Q h : Real}
    (hbound : ∀ D ∈ P, nu D ≤ h)
    (hcover : S1447SignedCoverage P nu Q) : Q ≤ h := by
  by_contra hnot
  have hlt : h < Q := lt_of_not_ge hnot
  let eps : Real := (Q - h) / 2
  have heps : 0 < eps := by
    dsimp [eps]
    linarith
  obtain ⟨D, hD, hDeps⟩ := hcover eps heps
  have hDh : nu D ≤ h := hbound D hD
  have hle : Q - eps ≤ h := le_trans hDeps hDh
  dsimp [eps] at hle
  linarith

/-- Consumer for the exact/signed output-readout projection. -/
theorem s1447Comparison_of_outputReadoutProjection
    {A : Type*} {P : Set A} {nu : A → Real} {Q h : Real}
    (hbound : ∀ D ∈ P, nu D ≤ h)
    (hproj : S1447OutputReadoutProjection P nu Q) : Q ≤ h := by
  rcases hproj with h | h
  · exact s1447Comparison_of_exactCoverage hbound h
  · exact s1447Comparison_of_signedCoverage hbound h

/-- The value-layer allowed source satisfies the exact projection.  This is
the constructed value-layer witness, not the paper final-evaluation family. -/
theorem s1447OutputReadoutProjection_valueLayer :
    S1447OutputReadoutProjection
      (allowedOutputSource I v R n) (readout I v)
      (I.sourceQPilotLogVolume v R n) :=
  Or.inl (valueLayerExactOutputWitness I v R n)

/-- The exact paper-level consumer: the output hull bound plus the missing
output-readout projection for the actual final-evaluation family imply the
fixed-C comparison.  The projection is a hypothesis here, never proved from
the value-layer witness. -/
theorem s1447PaperComparison_of_outputReadoutProjection
    {A : Type*} {P : Set A} {nu : A → Real}
    (hbound : ∀ D ∈ P, nu D ≤ I.sourceThetaHullLogVolume v R n)
    (hproj : S1447PaperOutputReadoutProjection (I := I) (v := v) (R := R) (n := n) P nu) :
    I.sourceQPilotLogVolume v R n ≤ I.sourceThetaHullLogVolume v R n :=
  s1447Comparison_of_outputReadoutProjection hbound hproj

#check c9IplComposite_eq_markedMap
#check qMark
#check qMark_eq_constant_qValue
#check qMark_mem_allowedOutputSource
#check qMark_mem_hull
#check readout_qMark_eq_card_mul_logDegree_q
#check readout_qMark_eq_sourceQSide
#check actualMarkedTrace
#check s1447Comparison_of_bdd
#check s1447ExactResidual_iff
#check s1447Comparison_of_contracted
#check readout_qMark_le_hullLog_of_bdd
#check s1136DataOfMarkedTrace
#check valueLayerExactOutputWitness
#check s1447Comparison_of_valueLayerExactWitness
#check qMarkAt_zero_eq_horizontal
#check readout_qMarkAt_eq
#check S1447ExactCoverage
#check S1447SignedCoverage
#check S1447OutputReadoutProjection
#check S1447PaperOutputReadoutProjection
#check s1447Comparison_of_signedCoverage
#check s1447Comparison_of_outputReadoutProjection
#check s1447OutputReadoutProjection_valueLayer
#check s1447PaperComparison_of_outputReadoutProjection

/-
Status of this file.

* The C9 trace cancellation is proved (`c9IplComposite_eq_markedMap`).
* The actual fixed-C q mark, value-layer theta-pilot source, same readout,
  exact value-layer witness, hull membership, monotone comparison, and the
  S1136 instantiation are proved.
* `S1447PaperOutputReadoutProjection P nu` is the exact paper-level residual
  for the actual final-evaluation family.  It is not constructed here, not an
  axiom, and not replaced by the value-layer witness.  Consequently the
  paper-level final-evaluation gate remains open; the value-layer file does
  not claim `target_accepted`.
-/

end LeanFormal.IUT.XiFPaper.S1447MarkedTraceActual

end