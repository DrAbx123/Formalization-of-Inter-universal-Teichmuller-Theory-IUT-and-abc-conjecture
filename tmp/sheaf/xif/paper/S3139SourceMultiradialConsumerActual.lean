import tmp.sheaf.xif.paper.S3139SourceMultiradialQuotientActual
import tmp.sheaf.xif.paper.S3139StageOneSeamsActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: named consumers of the multiradial-representation quotient carrier

This file exposes the actual partial multiradial target of
`S3139SourceMultiradialQuotientActual` as a *named input* for the lattice and
mainline streams (they can fill their consumers from it without editing this
file), wires it to the Stage-1 BPS/etHT demand of `S3139StageOneSeamsActual`,
and exposes the ultimate consumer: the q/Theta pilot log-volume comparison
heart of IUT III, Corollary 3.12.

What is actual (no arbitrary data):

* `SourceMultiradialTargetInput` bundles the actual quotient carrier, its
  quotient map and the descended log-volume/possible-image/level readouts
  together with the (Ind1)/(Ind2)/(Ind3) laws; `sourceMultiradialTargetInput`
  constructs the inhabitant;
* `sourceMultiradialEtHTTarget` is the etale-like portion `G_v` of the actual
  0-column etHT (Formalization :520-524), whose domain is the actual base
  theater of the source carrier;
* `SourceQThetaComparisonInput` is the named input of the q/Theta comparison
  heart: the S3138 source-level V2 pinned boundary, whose single arithmetic
  input is the (xi-f)-shaped inclusion `qSigned <= hullValue`.  Supplying it
  yields the Corollary 3.12 ordered conclusion; the lattice/mainline streams
  fill `qSigned`/`hullValue` from their actual pilot log-volumes.

Still exact-Missing (referenced, not constructed): the first-triangle
algorithmic mutation BPS -> the quotient target
(`SourceMultiradialMutationDemand`, Formalization :505-513).  No sorry, axiom,
True, PUnit, or toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139SourceMultiradialConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.MultiradialKernel.Core
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionProfileActual
open LeanFormal.IUT.XiFPaper.S3138SourceStepXIActual
open LeanFormal.IUT.XiFPaper.S3139SourceMultiradialQuotientActual
open LeanFormal.IUT.XiFPaper.S3139SourceEtHTActual
open LeanFormal.IUT.XiFPaper.S3139StageOneSeamsActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. Named multipradial target input for consumers -/

/-- Named consumable input: the actual quotient carrier together with its
quotient map and descended log-volume/possible-image/level readouts and the
(Ind1)/(Ind2)/(Ind3) laws.  The lattice and mainline streams can fill their
consumers from this record without editing this file. -/
structure SourceMultiradialTargetInput
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  carrier : Type ui
  map : SourceStepXIChoice I → carrier
  logVolume : carrier → ℝ
  possibleImage : carrier → Set ℝ
  level : carrier → ℕ
  map_ind1 : ∀ (g : SourceStepXILabel) (c : SourceStepXIChoice I),
    map ((sourceStepXICore I).ind1 g c) = map c
  map_ind2 : ∀ (g : SourceStepXILabel) (c : SourceStepXIChoice I),
    map ((sourceStepXICore I).ind2 g c) = map c
  logVolume_mk : ∀ c,
    logVolume (map c) = (sourceStepXIProfile I).logVolume c
  image_ind3_upper : ∀ (n : Nat) (c : SourceStepXIChoice I) (z : ℝ),
    z ∈ possibleImage (map c) →
      ∃ w, w ∈ possibleImage (map ((sourceStepXICore I).ind3 n c)) ∧ z ≤ w

/-- The actual multiradial target input. -/
noncomputable def sourceMultiradialTargetInput
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    SourceMultiradialTargetInput I where
  carrier := SourceMultiradialCarrier I
  map := sourceMultiradialMap I
  logVolume := sourceMultiradialLogVolume I
  possibleImage := sourceMultiradialPossibleImage I
  level := sourceMultiradialLevel I
  map_ind1 := sourceMultiradialMap_ind1 I
  map_ind2 := sourceMultiradialMap_ind2 I
  logVolume_mk := sourceMultiradialLogVolume_mk I
  image_ind3_upper := sourceMultiradialPossibleImage_ind3_upper I

/-! ## 2. The 0-column etHT radial target -/

/-- The radial target of the 0-column etHT: the etale-like portion `G_v` of
the vertical family link at the base column (Formalization :520-524). -/
def sourceMultiradialEtHTTarget
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V) : Type upi :=
  (SourceEtHT.sourceEtHTZeroColumn J 0).etaleLikePortion v

/-- The 0-column etHT domain is the actual base theater of the input, so the
radial target is read off the same actual object as the S3138 Step XI input. -/
theorem sourceMultiradialEtHTTarget_domain
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    (SourceEtHT.sourceEtHTZeroColumn J 0).domain = J.theaterAt 0 0 := rfl

/-- The target type of the still-missing first-triangle mutation: the
multiradial quotient carrier of the actual source core. -/
def sourceMultiradialMutationTarget
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) : Type ui :=
  SourceMultiradialCarrier J

/-! ## 3. Named input for the q/Theta comparison heart of Cor 3.12 -/

/-- Named input for the q/Theta pilot log-volume comparison (IUT III,
Corollary 3.12, heart): the S3138 source-level V2 pinned consumer shape with
the single (xi-f)-shaped inclusion as the named arithmetic input.  Supplying it
yields the ordered conclusion `-|log q| <= -|log Theta|` through the
source-level V2 boundary. -/
structure SourceQThetaComparisonInput
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  n : Int
  m : Int
  route : List (RouteStep SourceStepXILabel)
  qSigned : ℝ
  hullValue : ℝ
  q_negative : qSigned < 0
  xif : qSigned ≤ hullValue
  ipl : Prop
  she : Prop
  apt : Prop
  ipl_evidence : ipl
  she_evidence : she
  apt_evidence : apt

namespace SourceQThetaComparisonInput

variable {J : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C : SourceQThetaComparisonInput J)

/-- The source-level V2 pinned Step XI boundary determined by the named input. -/
noncomputable def boundary :=
  sourceStepXIBoundaryV2Hull J C.n C.m C.route C.qSigned C.hullValue
    C.q_negative C.xif C.ipl C.she C.apt C.ipl_evidence C.she_evidence
    C.apt_evidence

/-- The Corollary 3.12 ordered conclusion from the named q/Theta comparison
input. -/
theorem conclusion :
    Cor312Conclusion (C.boundary.assembly.arithmetic.toContract) :=
  sourceStepXIBoundaryV2Hull_contract J C.n C.m C.route C.qSigned
    C.hullValue C.q_negative C.xif C.ipl C.she C.apt C.ipl_evidence
    C.she_evidence C.apt_evidence

end SourceQThetaComparisonInput

end LeanFormal.IUT.XiFPaper.S3139SourceMultiradialConsumerActual

end
