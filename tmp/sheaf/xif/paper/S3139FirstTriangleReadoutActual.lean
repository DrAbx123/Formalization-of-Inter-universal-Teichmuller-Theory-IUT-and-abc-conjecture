import tmp.sheaf.xif.paper.S3139SourceMultiradialConsumerActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# S3139: post-mutation readouts for the q/Theta comparison

The first-triangle mutation of `S3139FirstTriangleMutationActual` outputs the
multiradial-representation point data (tensor packet, Ind1 action, LGP action,
F_mod^x copies).  This file exposes the readouts of that mutation that the
lattice/mainline streams consume for the q/Theta pilot log-volume comparison
(IUT III, Corollary 3.12; Formalization of IUT (2026-04) §4 :602-621):

* the descended multiradial quotient readouts with their (Ind1)/(Ind2)
  invariance and (Ind3) upper-semi;
* the actual signed q-pilot log-volume `-|log(q)|` from the actual Theta
  packet at the `(1,0)` column, proved negative once the actual q is not `1`;
* a constructor of the named `SourceQThetaComparisonInput` (the S3138 source
  V2 pinned boundary) from that actual q-pilot volume plus the signed hull
  value and the (xi-f)-shaped inclusion, together with the Corollary 3.12
  ordered conclusion.

The signed hull value and the inclusion remain the exact arithmetic input of
the fourth triangle (recorded in the S3138 residual); this file does not
manufacture them.  No sorry, axiom, True, PUnit, or toy carrier.

**Component, not paper object.**  Post-mutation readout interface; named future
consumers: the lattice/mainline q/Theta comparison and the S3134/S3138
fourth-triangle consumers (they fill the signed hull value/inclusion).
-/

namespace LeanFormal.IUT.XiFPaper.S3139FirstTriangleReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3139SourceMultiradialQuotientActual
open LeanFormal.IUT.XiFPaper.S3139SourceMultiradialConsumerActual
open LeanFormal.IUT.XiFPaper.S3139StageOneSeamsActual
open scoped TensorProduct

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. Descended multiradial readouts -/

/-- Post-mutation readout: (Ind1) acts trivially on the descended multiradial
quotient representation. -/
theorem mutationReadout_ind1_invariant
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (g : SourceStepXILabel) (c : SourceStepXIChoice J) :
    sourceMultiradialMap J ((sourceStepXICore J).ind1 g c) =
      sourceMultiradialMap J c :=
  sourceMultiradialMap_ind1 J g c

/-- Post-mutation readout: (Ind2) acts trivially on the descended multiradial
quotient representation. -/
theorem mutationReadout_ind2_invariant
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (g : SourceStepXILabel) (c : SourceStepXIChoice J) :
    sourceMultiradialMap J ((sourceStepXICore J).ind2 g c) =
      sourceMultiradialMap J c :=
  sourceMultiradialMap_ind2 J g c

/-- Post-mutation readout: the (Ind3) upper-semi inequality on the descended
possible log-volumes. -/
theorem mutationReadout_ind3_upper
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n : Nat) (c : SourceStepXIChoice J) (z : ℝ)
    (hz : z ∈ sourceMultiradialPossibleImage J (sourceMultiradialMap J c)) :
    ∃ w, w ∈ sourceMultiradialPossibleImage J
        (sourceMultiradialMap J ((sourceStepXICore J).ind3 n c)) ∧ z ≤ w :=
  sourceMultiradialPossibleImage_ind3_upper J n c z hz

/-! ## 2. The actual q-pilot signed log-volume -/

/-- The actual q-pilot signed log-volume `-|log q|` read from the actual Theta
packet q at the `(1,0)` column of the input. -/
noncomputable def sourceQPilotSignedLog
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) : ℝ :=
  -|Real.log ((J.theaterAt 1 0).thetaPacket.q)|

/-- The actual q is positive (`FiniteThetaPacket.q_pos`). -/
theorem sourceThetaQ_pos (J : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    0 < (J.theaterAt 1 0).thetaPacket.q :=
  (J.theaterAt 1 0).thetaPacket.q_pos

/-- The signed q-pilot log-volume is negative as soon as the actual q is not
`1`. -/
theorem sourceQPilotSignedLog_neg
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (hq : (J.theaterAt 1 0).thetaPacket.q ≠ 1) :
    sourceQPilotSignedLog J < 0 := by
  have hqpos : 0 < (J.theaterAt 1 0).thetaPacket.q := sourceThetaQ_pos J
  have hlog : Real.log ((J.theaterAt 1 0).thetaPacket.q) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hqpos hq
  exact neg_neg_of_pos (abs_pos.mpr hlog)

/-! ## 3. The named q/Theta comparison input from the mutation readouts -/

/-- Post-mutation q/Theta comparison input: the actual signed q-pilot
log-volume, the supplied signed hull value with the (xi-f)-shaped inclusion,
and explicit IPL/SHE/APT evidence. -/
noncomputable def sourceQThetaComparisonInputFromTheta
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (hq : (J.theaterAt 1 0).thetaPacket.q ≠ 1)
    (hullValue : ℝ) (hull_negative : hullValue < 0)
    (xif : sourceQPilotSignedLog J ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) : SourceQThetaComparisonInput J where
  n := n
  m := m
  route := route
  qSigned := sourceQPilotSignedLog J
  hullValue := hullValue
  q_negative := sourceQPilotSignedLog_neg J hq
  xif := xif
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := ipl_evidence
  she_evidence := she_evidence
  apt_evidence := apt_evidence

/-- The post-mutation q/Theta input yields the Corollary 3.12 ordered
conclusion through the S3138 source V2 boundary. -/
theorem sourceQThetaComparisonInputFromTheta_conclusion
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (hq : (J.theaterAt 1 0).thetaPacket.q ≠ 1)
    (hullValue : ℝ) (hull_negative : hullValue < 0)
    (xif : sourceQPilotSignedLog J ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    Cor312Conclusion
      ((sourceQThetaComparisonInputFromTheta J n m route hq hullValue
        hull_negative xif ipl she apt ipl_evidence she_evidence
        apt_evidence).boundary.assembly.arithmetic.toContract) :=
  (sourceQThetaComparisonInputFromTheta J n m route hq hullValue
    hull_negative xif ipl she apt ipl_evidence she_evidence
    apt_evidence).conclusion

end LeanFormal.IUT.XiFPaper.S3139FirstTriangleReadoutActual

end
