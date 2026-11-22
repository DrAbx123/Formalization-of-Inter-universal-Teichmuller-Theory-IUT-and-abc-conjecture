import tmp.sheaf.xif.paper.S3138SourceStepXIActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceProcessionStepXIMinimalForm
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# S3138: source-level Theorem 3.11 certificate and V1 Step XI boundary

Fifth piece of the source-level Step XI bridge.  Over the actual
`SourceProcessionBoundary.Input` built from a genuine `OriginalInput` this file
exposes the actual Theorem 3.11 certificate of the source procession boundary
(`SourceTheorem311Certificate`: source profile = actual theater Theta
log-volume, actual D-stage, actual Ind1/Ind2/Ind3 indeterminacy evidence, route
normalization) and instantiates the V1 two-field arithmetic link
(`ArithmeticLink`) and assembled V1 boundary (`SourceStepXIBoundary`) from the
single (xi-f)-shaped inclusion.

The certificate projections are definitional projections of the actual input
record; no new data is invented.  The V1 arithmetic link's second comparison is
proved from the pinning `target = theta = hullValue`.  IPL/SHE/APT evidence
stays explicit.

Source: IUT III, Theorem 3.11 and Corollary 3.12, Step (xi).
-/

namespace LeanFormal.IUT.XiFPaper.S3138SourceStepXIBoundaryActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.SourceProcessionStepXI
open LeanFormal.IUT.SourceProcessionBoundary
open LeanFormal.IUT.ParametricTheorem311
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionProfileActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCarrierActual
open LeanFormal.IUT.XiFPaper.S3138SourceStepXIActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. The actual source Theorem 3.11 certificate -/

/-- The actual source Theorem 3.11 certificate of the constructed boundary. -/
noncomputable def sourceStepXICertificate
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :=
  (sourceStepXIInput I n m).sourceTheorem311Certificate

/-- The certificate's source is the actual source carrier base choice. -/
theorem sourceStepXICertificate_source
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    (sourceStepXICertificate I n m).source =
      (sourceStepXIInput I n m).carrier.core.base :=
  (sourceStepXIInput I n m).sourceTheorem311Certificate_source

/-- The certificate's source profile is the actual theater Theta log-volume. -/
theorem sourceStepXICertificate_profile_eq_theta
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    (sourceStepXICertificate I n m).sourceProfile =
      (sourceStepXIInput I n m).theater.thetaPacket.logVolume :=
  (sourceStepXIInput I n m).sourceTheorem311Certificate_theta

/-- The certificate's Ind1 evidence is the actual Ind1 route certificate. -/
theorem sourceStepXICertificate_ind1
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (g : SourceStepXILabel) (c : SourceStepXIChoice I) :
    ((sourceStepXICertificate I n m).indeterminacy.ind1 g c).target =
      (sourceStepXIInput I n m).carrier.core.ind1 g c :=
  (sourceStepXIInput I n m).indeterminacy_ind1_target g c

/-- The certificate's Ind2 evidence is the actual Ind2 route certificate. -/
theorem sourceStepXICertificate_ind2
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (g : SourceStepXILabel) (c : SourceStepXIChoice I) :
    ((sourceStepXICertificate I n m).indeterminacy.ind2 g c).target =
      (sourceStepXIInput I n m).carrier.core.ind2 g c :=
  (sourceStepXIInput I n m).indeterminacy_ind2_target g c

/-- The certificate's Ind3 evidence is the actual Ind3 route certificate with
its vertical budget. -/
theorem sourceStepXICertificate_ind3
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (k : Nat) (c : SourceStepXIChoice I) :
    ((sourceStepXICertificate I n m).indeterminacy.ind3 k c).target =
      (sourceStepXIInput I n m).carrier.core.ind3 k c :=
  (sourceStepXIInput I n m).indeterminacy_ind3_target k c

/-- The certificate's route normalization is the actual parametric normal form
of the source carrier. -/
theorem sourceStepXICertificate_route_normalization
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel)) :
    ∃ b k,
      (sourceStepXIInput I n m).carrier.core.level b =
          (sourceStepXIInput I n m).carrier.core.level
            (sourceStepXIInput I n m).carrier.core.base ∧
        (sourceStepXIInput I n m).carrier.core.level
            (routeTarget (sourceStepXIInput I n m).carrier route
              (sourceStepXIInput I n m).carrier.core.base) =
          (sourceStepXIInput I n m).carrier.core.level b + k :=
  (sourceStepXIInput I n m).sourceTheorem311Certificate_route_normalization route

/-! ## 2. The V1 source-level arithmetic link and assembled boundary -/

/-- The source-level V1 arithmetic link from the explicit (xi-f) inclusion,
with the hull pinning `target = theta = hullValue`. -/
noncomputable def sourceStepXILinkV1Hull
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (qSigned hullValue : Real) (hq : qSigned < 0) (hle : qSigned ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :=
  arithmeticLinkOfHullInclusion (sourceStepXIInput I n m) route qSigned
    hullValue hq hle ipl she apt ipl_evidence she_evidence apt_evidence

/-- The assembled source-level V1 Step XI boundary from the explicit (xi-f)
inclusion. -/
noncomputable def sourceStepXIBoundaryV1Hull
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (qSigned hullValue : Real) (hq : qSigned < 0) (hle : qSigned ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :=
  sourceStepXIBoundary (sourceStepXIInput I n m) route
    (sourceStepXILinkV1Hull I n m route qSigned hullValue hq hle ipl she apt
      ipl_evidence she_evidence apt_evidence)

/-- Corollary 3.12 ordered conclusion over the actual source input, in the V1
two-field form. -/
theorem sourceStepXIBoundaryV1Hull_contract
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (qSigned hullValue : Real) (hq : qSigned < 0) (hle : qSigned ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    Cor312Conclusion
      (sourceStepXIBoundaryV1Hull I n m route qSigned hullValue hq hle
        ipl she apt ipl_evidence she_evidence apt_evidence).assembly.arithmetic.toContract :=
  sourceStepXIBoundary_contract (sourceStepXIInput I n m) route
    (sourceStepXILinkV1Hull I n m route qSigned hullValue hq hle ipl she apt
      ipl_evidence she_evidence apt_evidence)

/-- The V1 boundary's wall is the actual certificate wall of the source input. -/
theorem sourceStepXIBoundaryV1Hull_wall
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (qSigned hullValue : Real) (hq : qSigned < 0) (hle : qSigned ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    (sourceStepXIBoundaryV1Hull I n m route qSigned hullValue hq hle ipl she
      apt ipl_evidence she_evidence apt_evidence).wall =
      sourceStepXIWall I n m route := rfl

end LeanFormal.IUT.XiFPaper.S3138SourceStepXIBoundaryActual

end
