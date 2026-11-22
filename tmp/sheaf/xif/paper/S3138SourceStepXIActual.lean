import tmp.sheaf.xif.paper.S3138SourceProcessionCarrierActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceProcessionStepXI
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceProcessionStepXIInclusionResidual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# S3138: source-level Step XI assembly

Fourth piece of the source-level Step XI bridge.  Over the actual
`SourceProcessionBoundary.Input` built in
`S3138SourceProcessionCarrierActual` (theater at `(n,m)`, actual source
carrier, actual Theta log-volume), this file instantiates the Step XI objects
of `Corollary312/StepXI/`:

* the D-stage `Wall` of the parametric route (`routeWall`), including the
  actual run identity `wall.theorem311 = runAlgorithm carrier input`;
* the normalized wall (`NormalizedWall` / `normalizedWall`);
* the V2 pinned arithmetic link from the single (xi-f)-shaped inclusion
  `q <= hullValue` (`ArithmeticLinkV2` / `arithmeticLinkV2OfHullInclusion`)
  and the assembled `SourceStepXIBoundaryV2` with the Corollary 3.12 ordered
  conclusion;
* the nonnegative-hull version, where the inclusion slot is discharged from
  `0 <= hullValue` (the degenerate route of
  `SourceProcessionStepXIInclusionResidual`, same discriminating power as
  there: zero).

The paper's two arithmetic comparison facts and the IPL/SHE/APT evidence stay
explicit fields/arguments, exactly as in the corpus: nothing here manufactures
the signed hull comparison `-|log q| <= -|log Theta|`.  What is new is that the
whole Step XI assembly is now available over genuine source data instead of
only over the finite Q(i)-at-5 model.

Source: IUT III, Theorem 3.11 -> Corollary 3.12, Steps (xi-a)-(xi-f).
-/

namespace LeanFormal.IUT.XiFPaper.S3138SourceStepXIActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.SourceProcessionBoundary
open LeanFormal.IUT.SourceProcessionStepXI
open LeanFormal.IUT.ParametricStepXI
open LeanFormal.IUT.ParametricTheorem311
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionProfileActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCarrierActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. The D-stage wall over the actual source input -/

/-- The actual source-level Step XI wall for any route in the source lattice. -/
noncomputable def sourceStepXIWall
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel)) :=
  routeWall (sourceStepXIInput I n m) route

/-- The source-level wall's Theorem 3.11 output is the actual run of the
multiradial algorithm on the source algorithm input. -/
theorem sourceStepXIWall_output_is_run
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel)) :
    (sourceStepXIWall I n m route).wall.theorem311 =
      runAlgorithm (sourceStepXIInput I n m).carrier
        (sourceStepXIWall I n m route).routeOutput.algorithmInput :=
  wall_output_is_run (sourceStepXIInput I n m) route

/-- The source-level wall field is the actual certificate wall of its
algorithm input (definitional identification). -/
theorem sourceStepXIWall_wall
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel)) :
    (sourceStepXIWall I n m route).wall =
      stepXIWallCertificate (sourceStepXIInput I n m).carrier
        (sourceStepXIWall I n m route).routeOutput.algorithmInput := rfl

/-- The source-level wall's target is the route target from the source base. -/
theorem sourceStepXIWall_target
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel)) :
    (sourceStepXIWall I n m route).wall.theorem311.target =
      routeTarget (sourceStepXIInput I n m).carrier route
        (sourceStepXIInput I n m).carrier.core.base :=
  wall_target (sourceStepXIInput I n m) route

/-! ## 2. The normalized wall over the actual source input -/

/-- The actual source-level normalized wall: the route target is brought to
the normal form `ind3 budget horizontal` with an actual horizontal choice. -/
noncomputable def sourceStepXINormalizedWall
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel)) :=
  normalizedWall (sourceStepXIInput I n m) route

/-- Normal form of the source route target. -/
theorem sourceStepXINormalizedWall_target
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel)) :
    routeTarget (sourceStepXIInput I n m).carrier route
        (sourceStepXIInput I n m).carrier.core.base =
      (sourceStepXIInput I n m).carrier.core.ind3
        (sourceStepXINormalizedWall I n m route).budget
        (sourceStepXINormalizedWall I n m route).horizontal :=
  normalizedWall_target (sourceStepXIInput I n m) route

/-! ## 3. Pinned V2 arithmetic link and assembly over the source input -/

/-- The source-level V2 pinned arithmetic link from the single (xi-f)-shaped
inclusion `qSigned <= hullValue`; the middle comparison is definitional. -/
noncomputable def sourceStepXILinkV2Hull
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (qSigned hullValue : Real) (hq : qSigned < 0) (hle : qSigned ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :=
  arithmeticLinkV2OfHullInclusion (sourceStepXIInput I n m) route qSigned
    hullValue hq hle ipl she apt ipl_evidence she_evidence apt_evidence

/-- The source-level V2 pinned arithmetic link from a nonnegative hull value:
the inclusion is discharged by the sign comparison (degenerate route, no
discriminating power -- recorded, not claimed as the corpus comparison). -/
noncomputable def sourceStepXILinkV2NonnegHull
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (qSigned hullValue : Real) (hq : qSigned < 0) (hh : 0 ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :=
  arithmeticLinkV2OfNonnegativeHullValue (sourceStepXIInput I n m) route
    qSigned hullValue hq hh ipl she apt ipl_evidence she_evidence apt_evidence

/-- The assembled source-level V2 Step XI boundary from the explicit (xi-f)
inclusion. -/
noncomputable def sourceStepXIBoundaryV2Hull
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (qSigned hullValue : Real) (hq : qSigned < 0) (hle : qSigned ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :=
  sourceStepXIBoundaryV2 (sourceStepXIInput I n m) route
    (sourceStepXILinkV2Hull I n m route qSigned hullValue hq hle ipl she apt
      ipl_evidence she_evidence apt_evidence)

/-- Corollary 3.12 ordered conclusion over the actual source input, from the
single explicit inclusion `qSigned <= hullValue`. -/
theorem sourceStepXIBoundaryV2Hull_contract
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (qSigned hullValue : Real) (hq : qSigned < 0) (hle : qSigned ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    Cor312Conclusion
      (sourceStepXIBoundaryV2Hull I n m route qSigned hullValue hq hle
        ipl she apt ipl_evidence she_evidence apt_evidence).assembly.arithmetic.toContract :=
  sourceStepXIBoundaryV2_contract (sourceStepXIInput I n m) route
    (sourceStepXILinkV2Hull I n m route qSigned hullValue hq hle ipl she apt
      ipl_evidence she_evidence apt_evidence)

/-- Corollary 3.12 ordered conclusion over the actual source input from a
nonnegative hull value (degenerate route; the corpus-signed comparison is not
claimed). -/
theorem sourceStepXIBoundaryV2NonnegHull_contract
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (qSigned hullValue : Real) (hq : qSigned < 0) (hh : 0 ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    Cor312Conclusion
      ((sourceStepXIBoundaryV2 (sourceStepXIInput I n m) route
        (sourceStepXILinkV2NonnegHull I n m route qSigned hullValue hq hh
          ipl she apt ipl_evidence she_evidence apt_evidence)).assembly.arithmetic.toContract) :=
  sourceStepXIBoundaryV2_contract (sourceStepXIInput I n m) route
    (sourceStepXILinkV2NonnegHull I n m route qSigned hullValue hq hh
      ipl she apt ipl_evidence she_evidence apt_evidence)

end LeanFormal.IUT.XiFPaper.S3138SourceStepXIActual

end
