import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.IUTIII.Theorem311.Output.SourceMultiradialPresentationWiring
import LeanFormal.IUT.IUTIII.Theorem311.Output.SourceMultiradialIplLinkWiring
import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import tmp.sheaf.xif.paper.S1195ActualUpperEnv
import tmp.sheaf.xif.paper.S1170RouteTraceAuditActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteParameterized
import LeanFormal.IUT.IUTIII.Theorem311.ConcreteFiniteModel

/-! # SourceOutputPrimeStripInterpretation

A-integration content:

* SourceRun records the actual source algorithm run (input, actual
  runAlgorithm output, the conditional presentation/algorithm records) and
  forgetRun is its actual reduced output.
* actualUpperEnv is the S1195 actual non-refl evaluation arrow
  I.fPrimeStripAt 1 0 -> I.fPrimeStripAt 1 1, with actual stripIso and actual
  non-refl graph Kummer layer.
* The adjacent Kummer square is recorded as the exact existing type
  SourceKummerEvaluationSquare; no inhabitant is asserted.
* Nontriviality of upperEnv is a separate exact condition; it is not claimed.

The named consumer of the provenance is
LeanFormal.IUT.Audit.iplAlgorithmicProvenanceCard.
-/

noncomputable section

namespace LeanFormal.IUT.Theorem311.Output

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.ParametricTheorem311
open LeanFormal.IUT.SourceMultiradialPresentationWiring
open LeanFormal.IUT.XiFPaper.S1170RouteTraceAuditActual
open LeanFormal.IUT.XiFPaper.S1195ActualUpperEnv
open LeanFormal.IUT.SourceFiniteParameterized
open LeanFormal.IUT.ConcreteFiniteTheorem311

universe ua uv upi umon ui u v uG1 uG2

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type u} {Choice : Type v} [AddGroup Label]
variable {G1 : Type uG1} [Group G1] {G2 : Type uG2} [Group G2]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V} {n : Int}

/-- Actual source algorithm run: input, actual runAlgorithm output, conditional
presentation/algorithm records.  No Q<=H or q membership is stored. -/
structure SourceRun
    (C : Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData C G1)
    (ind2Data : Ind2ActionData C autom G2)
    (input : AlgorithmInput C) where
  output : AlgorithmOutput C input
  output_eq : output = runAlgorithm C input
  presentation : SourceTheorem311MultiradialPresentation G1 I n Choice
  presentation_eq : presentation =
    sourcePresentationOfCarrier (I := I) (n := n) C autom input
  algorithm : SourceTheorem311MultiradialAlgorithm G1 G2 I n Choice
  algorithm_eq : algorithm =
    sourceAlgorithmOfCarrier (I := I) (n := n) C autom ind2Data input

/-- Actual constructor for SourceRun. -/
noncomputable def sourceRun
    (C : Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData C G1)
    (ind2Data : Ind2ActionData C autom G2)
    (input : AlgorithmInput C) :
    SourceRun (I := I) (n := n) C autom ind2Data input where
  output := runAlgorithm C input
  output_eq := rfl
  presentation := sourcePresentationOfCarrier (I := I) (n := n) C autom input
  presentation_eq := rfl
  algorithm := sourceAlgorithmOfCarrier (I := I) (n := n) C autom ind2Data input
  algorithm_eq := rfl

/-- Actual forgetRun: the reduced output target of the run. -/
noncomputable def forgetRun
    (C : Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData C G1)
    (ind2Data : Ind2ActionData C autom G2)
    (input : AlgorithmInput C) : Choice :=
  (sourceRun (I := I) (n := n) C autom ind2Data input).output.target

/-- forgetRun is the runAlgorithm target, actually. -/
theorem forgetRun_eq_runAlgorithm_target
    (C : Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData C G1)
    (ind2Data : Ind2ActionData C autom G2)
    (input : AlgorithmInput C) :
    forgetRun (I := I) (n := n) C autom ind2Data input =
      (runAlgorithm C input).target := rfl

/-- The actual route trace alias (S1170); records intermediate choices. -/
noncomputable abbrev sourceRouteTrace
    (C : Carrier Label Choice) (input : AlgorithmInput C) :
    RouteTrace Choice :=
  routeTrace C input.route input.source

/-- The route trace endpoint is the reduced run target. -/
theorem sourceRouteTrace_endpoint
    (C : Carrier Label Choice) (input : AlgorithmInput C) :
    (sourceRouteTrace C input).endpoint = (runAlgorithm C input).target :=
  routeTrace_endpoint_eq_runAlgorithm_target C input

/-- Actual upperEnv strip pair. -/
abbrev S10 : FPrimeStrip.{umon, uv, upi} V := I.fPrimeStripAt 1 0
abbrev S11 : FPrimeStrip.{umon, uv, upi} V := I.fPrimeStripAt 1 1
abbrev S00 : FPrimeStrip.{umon, uv, upi} V := I.fPrimeStripAt 0 0

local instance s10Top : ∀ v : V, TopologicalSpace ((S10 (I := I)).Pi v) :=
  fun _ => ⊥
abbrev S01 : FPrimeStrip.{umon, uv, upi} V := I.fPrimeStripAt 0 1

/-- Actual S1195 non-refl upperEnv. -/
noncomputable abbrev actualUpperEnv :
    SourceEvaluationArrow (GG (I := I))
      (S10 (I := I)) (S11 (I := I)) :=
  upperEnv (I := I)

/-- Actual upperEnv strip is the actual fLinkAt 1 0 1 1. -/
theorem actualUpperEnv_stripIso :
    (actualUpperEnv).stripIso = I.fLinkAt 1 0 1 1 :=
  upperEnv_stripIso (I := I)

/-- Exact adjacent Kummer square data (no inhabitant asserted). -/
structure S1212AdjacentKummerSquareData where
  square : SourceKummerEvaluationSquare
    (GG (I := I))
    (S00 (I := I)) (S01 (I := I)) (S10 (I := I)) (S11 (I := I))

/-- Exact nontriviality condition for upperEnv; not claimed. -/
def S1212UpperEnvNontrivial : Prop :=
  ∃ (v : V) (g : GG (I := I)) (x : TimesMuQuotient (((S10 (I := I)).Mon v)ˣ)),
    TimesMuQuotient.action ((actualUpperEnv).unitPortion.sourceAction v) g x ≠ x


/-! ## Actual strip map on the source family index

For `Choice := I.family.index`, every actual source index yields an actual
F-prime-strip by `I.fPrimeStripAt` at the corresponding `Int × Int` label.
This is the first A-integration map: it does not construct a concrete
`SourceDefinition31Data` or `OriginalInput`; the theorem is for arbitrary `I`.
-/

/-- Actual strip attached to a source family index. -/
noncomputable def stripOfChoice (i : I.family.index) :
    FPrimeStrip.{umon, uv, upi} V :=
  I.fPrimeStripAt (I.index_equiv i).1 (I.index_equiv i).2

@[simp] theorem stripOfChoice_apply (i : I.family.index) :
    stripOfChoice (I := I) i =
      I.fPrimeStripAt (I.index_equiv i).1 (I.index_equiv i).2 := rfl

/-- The strip map is actual and total on the source family index. -/
theorem stripOfChoice_exists (i : I.family.index) :
    ∃ F : FPrimeStrip.{umon, uv, upi} V, F = stripOfChoice (I := I) i :=
  ⟨stripOfChoice (I := I) i, rfl⟩

/-- First A-integration target for arbitrary I: Choice = I.family.index, with
actual strip interpretation.  The next step is to build the algorithm
input/route on this Choice type; this declaration does not assert such a
route or a concrete initial instance. -/
def SourceFamilyChoice : Type ui := I.family.index


/-! ## Actual finite-kernel SourceRun instance (S1234 integration)

This is the actual finite-kernel run on the concrete finite carrier.  It uses
the W.1/W.4 datum `finiteKernelProcessionAutomorphism` and
`finiteKernelInd2ActionData` from the wiring file, and the actual
`AlgorithmInput.empty`.  It is an actual instance of the general SourceRun
above, not a new weak interface. -/

abbrev S1234L (l : PrimeGeFive) : Type := Multiplicative (finiteLabel l)

noncomputable abbrev s1234Autom (l : PrimeGeFive) :
    SourceProcessionAutomorphismData (SourceFiniteParameterized.carrier l) (S1234L l) :=
  finiteKernelProcessionAutomorphism l

noncomputable abbrev s1234Ind2 (l : PrimeGeFive) :
    Ind2ActionData (SourceFiniteParameterized.carrier l)
      (s1234Autom l) (S1234L l) :=
  finiteKernelInd2ActionData l

noncomputable abbrev s1234Input (l : PrimeGeFive) :
    AlgorithmInput (SourceFiniteParameterized.carrier l) :=
  AlgorithmInput.empty (SourceFiniteParameterized.carrier l)

noncomputable def finiteKernelRun
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    SourceRun (I := I) (n := 0)
      (C := SourceFiniteParameterized.carrier l)
      (s1234Autom l) (s1234Ind2 l) (s1234Input l) :=
  sourceRun (I := I) (n := 0)
    (C := SourceFiniteParameterized.carrier l)
    (s1234Autom l) (s1234Ind2 l) (s1234Input l)

theorem finiteKernelRun_forget
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    forgetRun (I := I) (n := 0)
      (C := SourceFiniteParameterized.carrier l)
      (s1234Autom l) (s1234Ind2 l) (s1234Input l) =
    (runAlgorithm (SourceFiniteParameterized.carrier l)
      (s1234Input l)).target :=
  forgetRun_eq_runAlgorithm_target (I := I) (n := 0)
    (C := SourceFiniteParameterized.carrier l)
    (s1234Autom l) (s1234Ind2 l) (s1234Input l)


end LeanFormal.IUT.Theorem311.Output

end