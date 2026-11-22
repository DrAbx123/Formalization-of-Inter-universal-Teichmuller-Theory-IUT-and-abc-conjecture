import tmp.sheaf.xif.paper.S3138SourceProcessionCarrierActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ParametricStepXI
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3138: source-level ParametricStepXI instantiation

This file instantiates the parametric Step XI assembly of
`Corollary312/StepXI/ParametricStepXI.lean` over the *actual source* carrier of
`S3138SourceProcessionCarrierActual` (built from a genuine `OriginalInput`),
together with the actual route output of the source procession boundary.

What is actual here: the carrier, the algorithm input/output and the wall
certificate, i.e. every object that `ParametricStepXI` constructs generically
from a carrier.  The scalar arithmetic data `qSigned`, `targetSigned`,
`thetaSigned` and the IPL/SHE/APT evidence are explicit parameters in the shape
required by `StepXIInput` -- they are the paper's arithmetic comparison inputs,
not constructible from the carrier alone.

Source: IUT III, Theorem 3.11 (multiradial algorithm) and Corollary 3.12,
Step (xi).  Consumer: `S3138SourceStepXIActual` (pinned V2 boundary).
-/

namespace LeanFormal.IUT.XiFPaper.S3138SourceParametricStepXIActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.SourceProcessionBoundary
open LeanFormal.IUT.ParametricStepXI
open LeanFormal.IUT.ParametricTheorem311
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionProfileActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCarrierActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. The actual source algorithm input and wall certificate -/

/-- The actual source algorithm input at the given route. -/
noncomputable def sourceStepXIAlgorithmInput
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel)) :=
  (sourceStepXIInput I n m).routeOutput route

/-- The actual source wall certificate over the source carrier. -/
noncomputable def sourceStepXIWallCertificateActual
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel)) :=
  stepXIWallCertificate (sourceStepXIInput I n m).carrier
    (sourceStepXIAlgorithmInput I n m route).algorithmInput

/-- The source wall certificate's Theorem 3.11 output is the actual run of the
multiradial algorithm. -/
theorem sourceStepXIWallCertificateActual_output_is_run
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel)) :
    (sourceStepXIWallCertificateActual I n m route).theorem311 =
      runAlgorithm (sourceStepXIInput I n m).carrier
        (sourceStepXIAlgorithmInput I n m route).algorithmInput :=
  stepXIWallCertificate_output (sourceStepXIInput I n m).carrier
    (sourceStepXIAlgorithmInput I n m route).algorithmInput

/-! ## 2. The actual source StepXIInput (arithmetic data explicit) -/

/-- The source `StepXIInput`: the actual source algorithm input and run, plus
the four explicit arithmetic fields. -/
noncomputable def sourceStepXIArithmeticInput
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (qSigned targetSigned thetaSigned : Real) (hq : qSigned < 0)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt)
    (hq_target : qSigned ≤ targetSigned)
    (htarget_theta : targetSigned ≤ thetaSigned) :=
  stepXIInput (sourceStepXIInput I n m).carrier
    (sourceStepXIAlgorithmInput I n m route).algorithmInput
    qSigned targetSigned thetaSigned hq ipl she apt
    ipl_evidence she_evidence apt_evidence hq_target htarget_theta

/-- The arithmetic contract slot of the source input data. -/
noncomputable def sourceStepXIArithmeticContract
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (qSigned targetSigned thetaSigned : Real) (hq : qSigned < 0)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt)
    (hq_target : qSigned ≤ targetSigned)
    (htarget_theta : targetSigned ≤ thetaSigned) :=
  StepXIInput.toContract
    (sourceStepXIArithmeticInput I n m route qSigned targetSigned thetaSigned
      hq ipl she apt ipl_evidence she_evidence apt_evidence hq_target
      htarget_theta)

/-- Corollary 3.12 ordered conclusion for the source arithmetic contract. -/
theorem sourceStepXIArithmeticContract_conclusion
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (qSigned targetSigned thetaSigned : Real) (hq : qSigned < 0)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt)
    (hq_target : qSigned ≤ targetSigned)
    (htarget_theta : targetSigned ≤ thetaSigned) :
    Cor312Conclusion
      (sourceStepXIArithmeticContract I n m route qSigned targetSigned
        thetaSigned hq ipl she apt ipl_evidence she_evidence apt_evidence
        hq_target htarget_theta) :=
  StepXIInput.conclusion
    (sourceStepXIArithmeticInput I n m route qSigned targetSigned thetaSigned
      hq ipl she apt ipl_evidence she_evidence apt_evidence hq_target
      htarget_theta)

/-! ## 3. The actual source StepXI assembly -/

/-- The assembled source `SourceStepXIAssembly`: actual wall plus the source
arithmetic input. -/
noncomputable def sourceStepXIAssemblyActual
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (qSigned targetSigned thetaSigned : Real) (hq : qSigned < 0)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt)
    (hq_target : qSigned ≤ targetSigned)
    (htarget_theta : targetSigned ≤ thetaSigned) :=
  sourceStepXIAssembly (sourceStepXIInput I n m).carrier
    (sourceStepXIAlgorithmInput I n m route).algorithmInput
    (sourceStepXIArithmeticInput I n m route qSigned targetSigned thetaSigned
      hq ipl she apt ipl_evidence she_evidence apt_evidence hq_target
      htarget_theta)

/-- The source assembly's wall agrees with its arithmetic output. -/
theorem sourceStepXIAssemblyActual_wall_input_agrees
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (qSigned targetSigned thetaSigned : Real) (hq : qSigned < 0)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt)
    (hq_target : qSigned ≤ targetSigned)
    (htarget_theta : targetSigned ≤ thetaSigned) :
    (sourceStepXIAssemblyActual I n m route qSigned targetSigned thetaSigned
        hq ipl she apt ipl_evidence she_evidence apt_evidence hq_target
        htarget_theta).wall.theorem311 =
      (sourceStepXIAssemblyActual I n m route qSigned targetSigned thetaSigned
        hq ipl she apt ipl_evidence she_evidence apt_evidence hq_target
        htarget_theta).arithmetic.output :=
  (sourceStepXIAssemblyActual I n m route qSigned targetSigned thetaSigned
    hq ipl she apt ipl_evidence she_evidence apt_evidence hq_target
    htarget_theta).wall_input_agrees

/-- Corollary 3.12 ordered conclusion of the assembled source Step XI boundary. -/
theorem sourceStepXIAssemblyActual_contract
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int)
    (route : List (RouteStep SourceStepXILabel))
    (qSigned targetSigned thetaSigned : Real) (hq : qSigned < 0)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt)
    (hq_target : qSigned ≤ targetSigned)
    (htarget_theta : targetSigned ≤ thetaSigned) :
    Cor312Conclusion
      (sourceStepXIAssemblyActual I n m route qSigned targetSigned thetaSigned
        hq ipl she apt ipl_evidence she_evidence apt_evidence hq_target
        htarget_theta).arithmetic.toContract :=
  sourceStepXIAssembly_conclusion (sourceStepXIInput I n m).carrier
    (sourceStepXIAlgorithmInput I n m route).algorithmInput
    (sourceStepXIArithmeticInput I n m route qSigned targetSigned thetaSigned
      hq ipl she apt ipl_evidence she_evidence apt_evidence hq_target
      htarget_theta)

end LeanFormal.IUT.XiFPaper.S3138SourceParametricStepXIActual

end
