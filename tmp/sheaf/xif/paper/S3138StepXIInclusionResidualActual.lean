import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceProcessionStepXIInclusionResidual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3138: exact residual of the Step (xi-f) signed hull comparison

This file records the *exact missing source object* of IUT III Corollary 3.12,
Step (xi-f), and proves everything that can be proved about it without
manufacturing the missing signed hull carrier.

Corpus anchors (IUT III, Corollary 3.12 proof, Step (xi)):

* (xi-d): `R^{<= -|log(Theta)|} := {lambda in R | lambda <= -|log(Theta)|}
  subset R; -|log(q)| in R`, where `-|log(Theta)|` is the (negative) log-volume
  of the holomorphic hull `1,circ U`;
* (xi-f): the inclusion `-|log(q)| in R^{<= -|log(Theta)|}`, hence
  `-|log(q)| <= -|log(Theta)|` in `R`.

The tree supplies only an ENNReal-valued IQ hull log-volume (nonnegative real
part) and the nonnegative-carrier wires of
`SourceProcessionStepXIInclusionResidual`, under which the inclusion is
automatic (zero discriminating power).  The genuine signed comparison needs the
missing `SignedHullRealization` below, whose scalar fields are demanded data,
not constructed here.  This file does NOT claim the signed carrier, does not
close the (xi-f) card, and introduces no axiom, sorry, or toy value.

Proved here (all unconditional):

* the scalar comparison is equivalent to the absolute-value comparison
  `|log Theta| <= |log q|`;
* the comparison is exactly `1 <= C_Theta` for the ratio
  `C_Theta = |log q| / |log Theta|`;
* the comparison is invariant under simultaneous positive rescaling of the two
  absolute log-volumes (it is scale-free, as in the procession-normalized
  reading of IUT IV, Theorem 1.10);
* sign data alone does NOT determine the comparison;
* a supplied `SignedHullRealization` yields the Corollary 3.12 ordered
  conclusion through the existing `StepXIContract` surface.
-/

namespace LeanFormal.IUT.XiFPaper.S3138StepXIInclusionResidualActual

open LeanFormal.IUT

/-! ## 1. The scalar signed comparison -/

/-- Exact demand record of Step (xi-f): a signed hull log-volume
`-|log(Theta)| < 0` for the holomorphic hull `1,circ U`, a signed q-pilot
log-volume `-|log(q)| < 0`, and the inclusion between them (III:10843-10898).
The positivity facts on the absolute log-volumes are kept so that the corpus
formula `-|log(-)|` is not replaced by an arbitrary negative real. -/
structure SignedHullRealization where
  /-- `|log q|` with `|log q| > 0` (the q-pilot log-volume is negative) -/
  qLogAbs : Real
  qLogAbs_pos : 0 < qLogAbs
  /-- `|log Theta|` with `|log Theta| > 0` (the Theta-pilot log-volume) -/
  thetaLogAbs : Real
  thetaLogAbs_pos : 0 < thetaLogAbs
  /-- the (xi-f) inclusion `-|log q| <= -|log Theta|` (III:10895-10898) -/
  xifInclusion : -qLogAbs ≤ -thetaLogAbs

namespace SignedHullRealization

/-- The q-pilot signed log-volume `-|log q|`. -/
def qPilotLog (G : SignedHullRealization) : Real := -G.qLogAbs

/-- The signed hull log-volume `-|log Theta|`. -/
def hullLog (G : SignedHullRealization) : Real := -G.thetaLogAbs

/-- The corpus sign facts: both signed log-volumes are negative. -/
theorem qPilotLog_neg (G : SignedHullRealization) : G.qPilotLog < 0 :=
  neg_neg_of_pos G.qLogAbs_pos

theorem hullLog_neg (G : SignedHullRealization) : G.hullLog < 0 :=
  neg_neg_of_pos G.thetaLogAbs_pos

/-- The inclusion is exactly the absolute-value comparison
`|log Theta| <= |log q|`. -/
theorem xifInclusion_iff_abs (G : SignedHullRealization) :
    G.qPilotLog ≤ G.hullLog ↔ G.thetaLogAbs ≤ G.qLogAbs := by
  unfold SignedHullRealization.qPilotLog SignedHullRealization.hullLog
  rw [neg_le_neg_iff]

/-- The corpus ratio: `C_Theta = |log q| / |log Theta|`. -/
def CTheta (G : SignedHullRealization) : Real :=
  G.qLogAbs / G.thetaLogAbs

/-- The (xi-f) inclusion is exactly `1 <= C_Theta`: the ratio form of the
comparison. -/
theorem xifInclusion_iff_CTheta (G : SignedHullRealization) :
    G.qPilotLog ≤ G.hullLog ↔ 1 ≤ G.CTheta := by
  rw [xifInclusion_iff_abs]
  unfold SignedHullRealization.CTheta
  rw [le_div_iff₀ G.thetaLogAbs_pos, one_mul]

/-- Comparison is invariant under simultaneous positive rescaling of the two
absolute log-volumes: it is a scale-free relative comparison. -/
theorem comparison_scale_invariant (G : SignedHullRealization)
    {c : Real} (hc : 0 < c) :
    (-(c * G.qLogAbs) ≤ -(c * G.thetaLogAbs)) ↔
      G.qPilotLog ≤ G.hullLog := by
  unfold SignedHullRealization.qPilotLog SignedHullRealization.hullLog
  rw [neg_le_neg_iff, neg_le_neg_iff]
  constructor
  · intro h
    exact le_of_mul_le_mul_left h hc
  · intro h
    exact mul_le_mul_of_nonneg_left h hc.le

end SignedHullRealization

/-! ## 2. Sign data does not determine the comparison -/

/-- Sign-only data of Step (xi-f): the corpus signs and absolute positivity,
i.e. the part that is forced by the definition of @-|log(-)|@, WITHOUT the
inclusion. -/
structure SignedLogData where
  /-- @|log q| > 0@ -/
  qLogAbs : Real
  qLogAbs_pos : 0 < qLogAbs
  /-- @|log Theta| > 0@ -/
  thetaLogAbs : Real
  thetaLogAbs_pos : 0 < thetaLogAbs

/-- The (xi-f) comparison as a predicate on sign-only data. -/
def SignedLogData.comparison (D : SignedLogData) : Prop :=
  -D.qLogAbs ≤ -D.thetaLogAbs

/-- The concrete sign-only data witnessing non-universality: @|log q| = 1@,
@|log Theta| = 2@. -/
noncomputable def signedLogDataCounterexample : SignedLogData where
  qLogAbs := 1
  qLogAbs_pos := by norm_num
  thetaLogAbs := 2
  thetaLogAbs_pos := by norm_num

/-- Sign data alone does not determine the (xi-f) inclusion: an admissible
sign-only data set in the corpus signs can fail the comparison.  The inclusion
therefore carries genuine arithmetic content (the negative result matches
@xifInclusion_signedSurface_counterexample@ of
@SourceProcessionStepXIInclusionResidual@, in the @-|log(-)|@ form). -/
theorem signedData_not_universal :
    ∃ D : SignedLogData, ¬ D.comparison := by
  refine ⟨signedLogDataCounterexample, ?_⟩
  unfold SignedLogData.comparison signedLogDataCounterexample
  norm_num

/-! ## 3. Consumer: the signed realization yields the Corollary 3.12 contract -/

/-- If the exact missing signed hull realization is supplied, then the
Corollary 3.12 ordered conclusion `-|log q| <= -|log Theta|` follows through
the existing `StepXIContract` surface (the middle element of the contract is
pinned at the hull value, so the second comparison is definitional).  The
IPL/SHE/APT evidence stays explicit, as in `Contract.lean`. -/
def contractOfSignedHullRealization (G : SignedHullRealization)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) : StepXIContract where
  qSigned := G.qPilotLog
  thetaSigned := G.hullLog
  targetSigned := G.hullLog
  q_negative := G.qPilotLog_neg
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := ipl_evidence
  she_evidence := she_evidence
  apt_evidence := apt_evidence
  q_le_target := G.xifInclusion
  target_le_theta := le_rfl

/-- Corollary 3.12 ordered conclusion from the signed hull realization. -/
theorem contractOfSignedHullRealization_conclusion (G : SignedHullRealization)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    Cor312Conclusion
      (contractOfSignedHullRealization G ipl she apt ipl_evidence
        she_evidence apt_evidence) :=
  cor312_of_constructed_stepXI
    (contractOfSignedHullRealization G ipl she apt ipl_evidence
      she_evidence apt_evidence)

/-- The contract's q slot is the signed q-pilot log-volume `-|log q|`. -/
theorem contractOfSignedHullRealization_qSigned (G : SignedHullRealization)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    (contractOfSignedHullRealization G ipl she apt ipl_evidence
      she_evidence apt_evidence).qSigned = G.qPilotLog := rfl

end LeanFormal.IUT.XiFPaper.S3138StepXIInclusionResidualActual

end
