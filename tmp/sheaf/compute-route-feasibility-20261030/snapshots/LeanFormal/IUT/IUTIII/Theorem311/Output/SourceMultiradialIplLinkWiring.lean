import LeanFormal.IUT.IUTIII.Theorem311.Output.SourceMultiradialPresentationWiring
import Mathlib.Tactic

/-!
# Reduced (IPL) link wiring: the "induced by operations in the algorithm" half

IUT III, Remark 3.11.1, (iii) (corpus III.txt:9676-9707) states the (Input
prime-strip link) (IPL) property of the output data of the Theorem 3.11
construction algorithm: the output data is linked/related, via full
poly-isomorphisms of F-turnstile-times-mu-prime-strips *induced by operations
in the algorithm*, to the input data prime-strip, i.e., the "coric"/"fixed"
q-pilot F-turnstile-times-mu-prime-strip equipped with its rigidifying
arithmetic holomorphic structure; and every "intermediate" prime-strip of
the construction may itself serve both as the input data of the algorithm and
-- via the linking poly-isomorphisms -- as the input data for the Kummer
theory surrounding the q-pilot object (III.txt:9688-9698).  The linking
isomorphisms are the composite of the inverses of the first two lower
horizontal arrows of the Remark 3.10.2 diagram, the first vertical arrow
(Kummer theory), and the three upper horizontal arrows (evaluation map);
cf. III.txt:9699-9707.

The F-turnstile-times-mu-prime-strip face of (IPL) is carried by the parallel
line `SourceFTimesMuPrimeStripPolyIsomorphism.lean` (read-only here: carrier
at :164, full poly-isomorphism classes at :585, the Remark 3.10.2 diagram
contract at :805 and its IPL composite `iplLink` at :845; the header of that
file explicitly leaves open the clause "induced by operations in the
algorithm" and the bridge to the source-level link factorization).  This file
proves the part of that clause which the reduced algorithm interface of
`SourceMultiradialPresentationWiring` can express:

* `ReducedIplLink`: the output is the route-operation image of the input
  source (the link is *by operations in the algorithm*); every intermediate
  stage of the route (a prefix) can equally serve as the input of the
  algorithm for the remaining operations, with the same output (the
  intermediate-strip dual role); and the link is compatible with the
  procession automorphisms (W.2b).
* `reducedIplLink_holds`: the reduced link holds for every carrier, every
  W.1 automorphism datum and every algorithm input.
* `finiteKernelReducedIplLink`: the Q(i)-at-5 finite kernel instance.

Reduced form, explicitly: the reduced interface has no prime-strip object
attached to the algorithm output (no correspondence between the carrier
choice type and `FPrimeStrip V` is modeled anywhere in the tree -- the same
reason W.3 is unexpressible, see the wiring file header), so this file does
not restate the poly-isomorphism face and does not claim the source-level
(IPL).  The remaining provenance gap is recorded as the named card
`IUT-III.IPL.algorithmic-provenance` in the audit section below.
-/

namespace LeanFormal.IUT

noncomputable section

universe uG₁ u v

namespace SourceMultiradialIplLinkWiring

open MultiradialKernel
open MultiradialKernel.Core

variable {Label : Type u} {Choice : Type v} [AddGroup Label]
variable {G₁ : Type uG₁} [Group G₁]

/-- The algorithm input whose source is the intermediate stage reached by the
    route prefix `p`, continuing with the suffix `s`: the reduced form of the
    paper's intermediate prime-strip taken as the input data of the algorithm
    (III.txt:9688-9698). -/
def iplIntermediateInput (carrier : ParametricTheorem311.Carrier Label Choice)
    (input : ParametricTheorem311.AlgorithmInput carrier)
    (p s : List (RouteStep Label)) :
    ParametricTheorem311.AlgorithmInput carrier where
  source := ParametricTheorem311.routeTarget carrier p input.source
  route := s
  source_image_nonempty := carrier.profile.possibleImage_nonempty _

/-- The intermediate input runs to the same output: the prefix operations
    reach the intermediate stage, and the remaining operations drive it to
    the original output (composition of the algorithm's operations). -/
theorem iplIntermediateInput_target
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (input : ParametricTheorem311.AlgorithmInput carrier)
    (p s : List (RouteStep Label)) (h : input.route = p ++ s) :
    (ParametricTheorem311.runAlgorithm carrier
        (iplIntermediateInput carrier input p s)).target =
      (ParametricTheorem311.runAlgorithm carrier input).target := by
  simp only [iplIntermediateInput, ParametricTheorem311.runAlgorithm_target,
    ParametricTheorem311.algorithmTarget]
  rw [h, ParametricTheorem311.routeTarget_append]

/-- Reduced (IPL) link data at the algorithm interface: the "induced by
    operations in the algorithm" half of (III.txt:9676-9707) in the reduced
    interface.  The F-turnstile-times-mu poly-isomorphism itself is *not*
    part of this structure: no prime-strip object exists at this interface
    (see the file header). -/
structure ReducedIplLink (carrier : ParametricTheorem311.Carrier Label Choice)
    (autom : SourceMultiradialPresentationWiring.SourceProcessionAutomorphismData
      carrier G₁)
    (input : ParametricTheorem311.AlgorithmInput carrier) : Prop where
  /-- the output is the route-operation image of the input source -/
  target_eq : (ParametricTheorem311.runAlgorithm carrier input).target =
    ParametricTheorem311.routeTarget carrier input.route input.source
  /-- the intermediate-strip dual role: every prefix stage can be taken as
      the algorithm's input for the remaining operations, with the same
      output -/
  intermediate_compose : ∀ (p s : List (RouteStep Label)),
    input.route = p ++ s →
      (ParametricTheorem311.runAlgorithm carrier
          (iplIntermediateInput carrier input p s)).target =
        (ParametricTheorem311.runAlgorithm carrier input).target
  /-- compatibility with the procession automorphisms (W.2b) -/
  automorphism_compatible : ∀ (g : G₁),
    autom.act g (ParametricTheorem311.runAlgorithm carrier input).target =
      ParametricTheorem311.routeTarget carrier input.route
        (autom.act g input.source)

/-- The reduced (IPL) link holds for every carrier, every W.1 automorphism
    datum and every algorithm input: conditional only on those objects. -/
theorem reducedIplLink_holds
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (autom : SourceMultiradialPresentationWiring.SourceProcessionAutomorphismData
      carrier G₁)
    (input : ParametricTheorem311.AlgorithmInput carrier) :
    ReducedIplLink carrier autom input where
  target_eq := rfl
  intermediate_compose := fun p s h =>
    iplIntermediateInput_target carrier input p s h
  automorphism_compatible := fun g =>
    SourceMultiradialPresentationWiring.automorphism_runAlgorithm_target
      carrier autom g input

section FiniteKernel

open ConcreteFiniteTheorem311

/-- The Q(i)-at-5 finite kernel instance of the reduced (IPL) link, with W.1
    the finite kernel automorphism datum, for every algorithm input. -/
theorem finiteKernelReducedIplLink (l : PrimeGeFive)
    (input : ParametricTheorem311.AlgorithmInput
      (SourceFiniteParameterized.carrier l)) :
    ReducedIplLink (SourceFiniteParameterized.carrier l)
      (SourceMultiradialPresentationWiring.finiteKernelProcessionAutomorphism l)
      input :=
  reducedIplLink_holds _ _ input

end FiniteKernel

end SourceMultiradialIplLinkWiring

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record: the reduced-wiring fragment of (IPL) -- the "induced by
    operations in the algorithm" half at the reduced interface. -/
def sourceIplLinkWiringRecord : Obligation :=
  { id := "IUT-III.IPL.reduced-wiring"
    source :=
      "IUT III, Remark 3.11.1, (iii) (corpus III.txt:9676-9707: the (IPL) " ++
        "bullets, including the intermediate-prime-strip dual role at " ++
        ":9688-9698); Corollary 3.12 proof, Step (xi-a)"
    status := VerificationStatus.conditional
    note :=
      "`ReducedIplLink` (this file) proves, at the reduced algorithm " ++
        "interface: (1) the output is the route-operation image of the input " ++
        "source; (2) every intermediate stage of the route can serve as the " ++
        "algorithm's input for the remaining operations, with the same " ++
        "output (the intermediate-strip dual role); (3) the link is " ++
        "compatible with the procession automorphisms (W.2b, " ++
        "`automorphism_runAlgorithm_target`).  `reducedIplLink_holds` " ++
        "supplies it for every carrier, W.1 datum and input; " ++
        "`finiteKernelReducedIplLink` is the Q(i)-at-5 instance.  Reduced " ++
        "form, explicitly: this is the 'induced by operations in the " ++
        "algorithm' half only.  The F-turnstile-times-mu poly-isomorphism " ++
        "face is carried by the parallel line " ++
        "SourceFTimesMuPrimeStripPolyIsomorphism.lean (read-only; " ++
        "conditional diagram contract at :805, `iplLink` at :845, SHA " ++
        "12F251458A30B625375C9C2A0A1BB120C55D9F84083D439DC7BCCEC7CBC02864) " ++
        "and is not duplicated here; the algorithmic provenance of its " ++
        "arrows and the bridge to the source-level factorization remain " ++
        "the named card `IUT-III.IPL.algorithmic-provenance`.  No " ++
        "source-level (IPL) conclusion is asserted."
    dependsOn :=
      [ "IUT-III.multiradial-algorithm.source-presentation-wiring" ] }

/-- Named card: the algorithmic provenance of the Remark 3.10.2 diagram
    arrows of (IPL) and the bridge to the source-level link factorization;
    this is where the reduced wiring stops. -/
def iplAlgorithmicProvenanceCard : Obligation :=
  { id := "IUT-III.IPL.algorithmic-provenance"
    source :=
      "IUT III, Remark 3.11.1, (iii), composition formula (corpus " ++
        "III.txt:9699-9707) and the clause 'induced by operations in the " ++
        "algorithm' (III.txt:9683-9687)"
    status := VerificationStatus.pending
    note :=
      "Object: a realization attaching to every operation of the Theorem " ++
        "3.11 construction algorithm the corresponding full " ++
        "poly-isomorphism arrow of the Remark 3.10.2 diagram of " ++
        "SourceFTimesMuPrimeStripPolyIsomorphism.lean (arrow slots :809-836, " ++
        "`iplLink` :845) -- the algorithmic provenance of the diagram arrows " ++
        "-- together with the named bridge from the source-level link " ++
        "factorization to the input data (q-pilot) prime-strip.  " ++
        "Quantifier: per operation/arrow of the construction, for every " ++
        "(xi) configuration.  Assumptions: the diagram contract (arrows as " ++
        "data; that file's conditional form), the actual algorithm " ++
        "realization over the actual source strips (the same source-data " ++
        "face as `IUT-III.source-APT-transport-supply`, APT.lean:457), and " ++
        "a correspondence between algorithm operations and strip arrows.  " ++
        "Conclusion: the diagram's arrows are induced by algorithm " ++
        "operations, hence `iplLink` is the source-level composite of the " ++
        "construction and its relation to the q-pilot input prime-strip " ++
        "holds.  Consumers: the Step-XI contract (ipl : Prop slot, " ++
        "Contract.lean:37-40), the two APT site assemblies as the ipl " ++
        "hypothesis (APT.lean:370, :395), and the transport-supply card.  " ++
        "Three routes attempted and blocked: (a) a direct functor from " ++
        "route operations/stages to SourceFTimesMuPrimeStrip V -- no such " ++
        "functor exists in the tree and the reduced interface has no " ++
        "prime-strip object; (b) through the F-prime-strip level " ++
        "(FPrimeStripEquiv, `canonicalLift` :343 of the strip file) -- no " ++
        "bridge from FPrimeStrip V to the algorithm's Output/choice type is " ++
        "modeled anywhere (the same reason W.3 is unexpressible, wiring " ++
        "file header; the forwarded FPrimeStrip wiring request recorded in " ++
        "StepXI/SourceColumnCarrierIdentification.lean R6); (c) through the " ++
        "reduced consumption path of SourcePolyIsoTransportLaws.lean " ++
        "(CardIPLTransportSupply O1-O4, :313) -- it takes the transport " ++
        "data (LinkSpan, KummerEvaluationFactor) as fields and constructs " ++
        "no provenance.  The gate-level finite IPL squares " ++
        "(StepXI/FiniteSourceColumnTrunkBridge.lean; api5 report section " ++
        "16.2), the reflexive-transport/landing exchange (api5 report " ++
        ":188) and the reduced exchange laws (SourcePolyIsoTransportLaws) " ++
        "are already recorded elsewhere and are deliberately not " ++
        "duplicated.  Reopening requires one of: a strip family attached to " ++
        "the algorithm (the Definition 3.1 (D3)/(D4) face), the named " ++
        "bridge FPrimeStrip V -> Choice/Output, or a provenance " ++
        "construction for the O1-O4 supply fields.  Relation to the " ++
        "transport-supply card `IUT-III.source-APT-transport-supply` " ++
        "(APT.lean:457; cross-line entry #11): this card is the (IPL)-half " ++
        "evidence input of that supply, which additionally requires the " ++
        "(SHE) landing half; neither card entails the other.  PARKED at " ++
        "this named card.  The reduced wiring fragment " ++
        "(`ReducedIplLink`, `IUT-III.IPL.reduced-wiring`) is not an " ++
        "impersonation of it."
    dependsOn :=
      [ "IUT-III.IPL",
        "IUT-III.IPL.reduced-wiring",
        "IUT-III.source-APT-transport-supply" ] }

end LeanFormal.IUT.Audit
