import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3132SourceHolomorphicHullReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open scoped BigOperators

universe ua uv upi umon ui uMon

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-!
# Actual paper holomorphic hull readout (Remark 3.9.5)

The actual source holomorphic hull is defined in `SourceImageHull.lean` as the
least candidate `lambda.O` hull of the value-realized union of possible
theta-pilot images:

    `sourceHolomorphicHull = holomorphicHull sourceScalingUnits possibleThetaPilotImageSet`

with the candidate hull condition of Remark 3.9.5, (i) and the intersection
formula `phi(P) = inter_{H contains P} H` of Remark 3.9.5, (ii).  This module
extracts the readout of that actual hull operator in the paper form:

* membership is exactly membership in every candidate hull containing the
  possible image (`mem_sourceHolomorphicHull_iff`);
* the hull is the least such candidate hull
  (`sourceHolomorphicHull_least`, `sourceHolomorphicHull_eq_self`);
* the hull is stable under every actual scaling
  (`sourceHolomorphicHull_scaling_mul_mem`);
* the possible image is contained in the hull
  (`possibleThetaPilotImage_subset_hull_readout`);
* the paper hull operator is monotone and idempotent on the actual source data
  (`holomorphicHull_monotone_readout`,
  `sourceHolomorphicHull_idempotent_readout`).

Source: IUT III, Remark 3.9.5, (i), (ii); Corollary 3.12 proof (holomorphic hull
of `n,circ U_{j,vQ}`).  Only object properties are asserted; the H_C numerical
readout on an actual carrier is supplied separately (S3129/S3132 files).
-/

/-- **Paper membership characterization of the actual source holomorphic hull.**
A value point lies in the actual hull exactly when it lies in every candidate
`lambda.O` hull containing the actual possible theta-pilot image.  This is the
paper formula `phi(P) = inter_{H contains P} H` of Remark 3.9.5, (ii). -/
theorem mem_sourceHolomorphicHull_iff
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint v) :
    x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ↔
      ∀ H : Submonoid (I.ThetaPilotPoint v),
        CandidateHull (I.sourceScalingUnits v) H →
          I.possibleThetaPilotImageSet v R n ⊆ (H : Set (I.ThetaPilotPoint v)) →
            x ∈ H :=
  mem_holomorphicHull_iff

/-- **Readout containment.**  The actual possible theta-pilot image is
contained in the actual holomorphic hull. -/
theorem possibleThetaPilotImage_subset_hull_readout
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.possibleThetaPilotImageSet v R n ⊆
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) :=
  I.possibleThetaPilotImage_subset_sourceHolomorphicHull v R n

/-- **Leastness of the actual hull.**  The actual source holomorphic hull is
contained in every candidate hull that contains the possible image. -/
theorem sourceHolomorphicHull_least
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {H : Submonoid (I.ThetaPilotPoint v)}
    (hH : CandidateHull (I.sourceScalingUnits v) H)
    (hS : I.possibleThetaPilotImageSet v R n ⊆ (H : Set (I.ThetaPilotPoint v))) :
    I.sourceHolomorphicHull v R n ≤ H :=
  I.sourceHolomorphicHull_le v R n hH hS

/-- **P1 readout: the hull of a candidate hull is itself.**  For every candidate
`lambda.O` hull, the actual paper hull operator fixes it. -/
theorem sourceHolomorphicHull_eq_self_readout
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {H : Submonoid (I.ThetaPilotPoint v)}
    (hH : CandidateHull (I.sourceScalingUnits v) H) :
    holomorphicHull (I.sourceScalingUnits v) (H : Set (I.ThetaPilotPoint v)) = H :=
  I.sourceHolomorphicHull_eq_self v R n hH

/-- **Scaling stability of the actual hull readout.**  The actual source
holomorphic hull is stable under multiplication by every actual scaling. -/
theorem sourceHolomorphicHull_scaling_mul_mem
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {s : I.ThetaPilotPoint v} (hs : s ∈ I.sourceScalingUnits v)
    {x : I.ThetaPilotPoint v}
    (hx : x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))) :
    s * x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) :=
  I.sourceHolomorphicHull_scaling_mem v R n hs hx

/-- **Idempotence readout.**  Hulling the actual hull returns the actual hull. -/
theorem sourceHolomorphicHull_idempotent_readout
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    holomorphicHull (I.sourceScalingUnits v)
        (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) =
      I.sourceHolomorphicHull v R n :=
  I.sourceHolomorphicHull_idempotent v R n

/-- **Monotonicity readout of the paper hull operator.**  The actual paper hull
operator `phi` is monotone on sets of value points. -/
theorem holomorphicHull_monotone_readout
    (v : V) {S T : Set (I.ThetaPilotPoint v)} (hST : S ⊆ T) :
    holomorphicHull (I.sourceScalingUnits v) S ≤
      holomorphicHull (I.sourceScalingUnits v) T :=
  le_holomorphicHull_of_le hST

#check mem_sourceHolomorphicHull_iff
#check possibleThetaPilotImage_subset_hull_readout
#check sourceHolomorphicHull_least
#check sourceHolomorphicHull_scaling_mul_mem
#check sourceHolomorphicHull_idempotent_readout
#check holomorphicHull_monotone_readout

end LeanFormal.IUT.XiFPaper.S3132SourceHolomorphicHullReadoutActual

end
