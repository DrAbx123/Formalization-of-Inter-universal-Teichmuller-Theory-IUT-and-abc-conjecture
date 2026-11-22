import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteOutput
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

/-!
# Field-level law bundle of the concrete Q(i)-at-5 source output

Task (2026-10-16): item 17 output side of `IUT-III.theorem-3.11-output`
(`Theorem311/Obligations.lean:5`, status pending: "Construct the multiradial
output over the actual IUT I-II data").  Evaluation result: the general output
body is blocked on the source input package `Theorem311Source.Input`
(see `theorem311SourceInputResidual` below); the finite Q(i)-at-5 carrier is the
highest feasible constructive step on this side in the repository, and its
output object `SourceFiniteTheorem311.Output l` previously exposed its laws
only as separate theorems.

This file declares those laws in consumer-facing interface shape:

* `SourceFiniteTheorem311.OutputLawBundle l` is the field-level law bundle of
  the concrete output, shaped after the source-level bundle
  `MultiradialAlgorithmReduction.SourceOutputLawBundle`
  (`Output/MultiradialAlgorithmReduction.lean:461`) restricted to what the
  concrete carrier can express: the structural alignment of the three assembled
  parts, the procession-normalized log-volume and possible-image laws, the
  Ind1/Ind2/Ind3 quotient laws, and the algebraic-theta compatibility laws.
* `SourceFiniteTheorem311.output_lawBundle` proves the canonical instance
  `SourceFiniteTheorem311.output l` satisfies the bundle, with every field
  supplied by an existing proved declaration in `SourceFiniteOutput.lean` /
  `SourceFiniteMultiradial.lean` (listed in the doc comments of the structure
  fields).  No new mathematical content is introduced; this is the frozen
  consumer-facing interface and its finite-carrier discharge.

Reduced-form label: this bundle is the finite Q(i)-at-5 instance of the output
law interface.  It is not, and must not be cited as, the general source output
`Theorem311Source.theorem311Output I`, nor as the corpus Theorem 3.11 statement;
the general case remains conditional on `Theorem311Source.Input`
(`sourceMultiradialOutputDischarge`) with the source-input instantiation
recorded as the residual card `theorem311SourceInputResidual` at the end of
this file.

Corpus anchors (IUT III, Theorem 3.11): opening data III:9151-9163 (initial
Theta-data and a collection of distinct Hodge theaters); (i) Multiradial
Representation and the procession of D-prime-strips III:9164-9175.  The finite
carrier here is the repo's Q(i)-at-5 test carrier, which is not the paper's
collection of Hodge theaters.
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

local instance primeFactForSourceFiniteOutputLawBundle (l : PrimeGeFive) :
    Fact (Nat.Prime l.value) := l.factPrime

namespace SourceFiniteTheorem311

open ConcreteFiniteTheorem311

/-- Field-level law bundle of the concrete Q(i)-at-5 source output: the frozen
consumer-facing interface of the laws of `SourceFiniteTheorem311.output l`,
grouped as (a) alignment of the three assembled parts, (b) normalization anchors
of the log-volume, (c) procession profile laws, (d) quotient laws, (e)
algebraic-theta compatibility laws.  Every field is supplied for the canonical
instance by an existing proved declaration; the supplying declaration is named
in each field's doc comment. -/
structure OutputLawBundle (l : PrimeGeFive) : Prop where
  /-- `SourceFiniteTheorem311.output_history_terminal`. -/
  history_terminal_agrees :
    (output l).history.terminal = (output l).procession.sourceTheater
  /-- The `history_level_eq_algebraic_level` field of `Output`. -/
  history_level_agrees :
    (output l).history.level = (output l).algebraic.level
  /-- `SourceFiniteTheorem311.output_models_agree`. -/
  history_model_agrees :
    (output l).history.sourceModel = (output l).algebraic.sourceModel
  /-- `SourceFiniteTheorem311.procession_base_log_volume`. -/
  base_logVolume_eq_thetaLogVolume :
    (output l).procession.logVolume (output l).procession.baseChoice =
      ConcreteSourceEtaleThetaBridge.thetaLogVolume l
  /-- `SourceFiniteTheorem311.output_history_packet_volume`. -/
  history_packet_volume :
    (output l).history.terminal.thetaPacket.logVolume =
      ConcreteSourceEtaleThetaBridge.thetaLogVolume l
  /-- `SourceFiniteTheorem311.procession_log_volume_is_source_profile`. -/
  logVolume_formula :
    ∀ c : ProcessionChoice l,
      (output l).procession.logVolume c =
        ConcreteSourceEtaleThetaBridge.thetaLogVolume l +
          (c.upperSemiLevel : Real)
  /-- `SourceFiniteTheorem311.procession_ind1_invariant`. -/
  logVolume_ind1_invariant :
    ∀ (t : finiteLabel l) (c : ProcessionChoice l),
      (output l).procession.logVolume (ProcessionChoice.ind1Act t c) =
        (output l).procession.logVolume c
  /-- `SourceFiniteTheorem311.procession_ind2_invariant`. -/
  logVolume_ind2_invariant :
    ∀ (t : finiteLabel l) (c : ProcessionChoice l),
      (output l).procession.logVolume (ProcessionChoice.ind2Act t c) =
        (output l).procession.logVolume c
  /-- `SourceFiniteTheorem311.procession_ind3_upper`. -/
  logVolume_ind3_upper :
    ∀ (n : Nat) (c : ProcessionChoice l),
      (output l).procession.logVolume c ≤
        (output l).procession.logVolume (ProcessionChoice.ind3Lift n c)
  /-- `SourceFiniteTheorem311.procession_possible_nonempty`. -/
  possibleImage_nonempty :
    ∀ c : ProcessionChoice l,
      ((output l).procession.possibleImage c).Nonempty
  /-- `SourceFiniteTheorem311.procession_possible_ind1`. -/
  possibleImage_ind1 :
    ∀ (t : finiteLabel l) (c : ProcessionChoice l),
      (output l).procession.possibleImage (ProcessionChoice.ind1Act t c) =
        (output l).procession.possibleImage c
  /-- `SourceFiniteTheorem311.procession_possible_ind2`. -/
  possibleImage_ind2 :
    ∀ (t : finiteLabel l) (c : ProcessionChoice l),
      (output l).procession.possibleImage (ProcessionChoice.ind2Act t c) =
        (output l).procession.possibleImage c
  /-- `SourceFiniteTheorem311.procession_possible_ind3_upper`. -/
  possibleImage_ind3_upper :
    ∀ (n : Nat) (c : ProcessionChoice l) (z : Real),
      z ∈ (output l).procession.possibleImage c →
        ∃ w, w ∈ (output l).procession.possibleImage
          (ProcessionChoice.ind3Lift n c) ∧ z ≤ w
  /-- `SourceFiniteTheorem311.procession_generated_quotient_same_level`. -/
  quotient_same_level :
    ∀ {a b : ProcessionChoice l},
      a.upperSemiLevel = b.upperSemiLevel →
        generatedQuotientMap l a = generatedQuotientMap l b
  /-- `SourceFiniteTheorem311.procession_generated_quotient_no_level_collapse`. -/
  quotient_level_separation :
    ∀ {a b : ProcessionChoice l},
      a.upperSemiLevel ≠ b.upperSemiLevel →
        generatedQuotientMap l a ≠ generatedQuotientMap l b
  /-- `SourceFiniteTheorem311.procession_quotient_image_nonempty`. -/
  quotient_image_nonempty :
    ∀ q : generatedQuotient l,
      (quotientPossibleLogImage l q).Nonempty
  /-- `SourceFiniteTheorem311.procession_quotient_ind3_upper`. -/
  quotient_image_ind3_upper :
    ∀ (a : ProcessionChoice l) (n : Nat) (z : Real),
      z ∈ quotientPossibleLogImage l (generatedQuotientMap l a) →
        ∃ w, w ∈ quotientPossibleLogImage l
          (generatedQuotientMap l (ProcessionChoice.ind3Lift n a)) ∧ z ≤ w
  /-- `SourceFiniteTheorem311.output_reduction_kernel`. -/
  reduction_kernel :
    (ConcreteSourceEtaleThetaBridge.reduction l).ker =
      AddSubgroup.zmultiples (l.value : ℤ)
  /-- `SourceFiniteTheorem311.output_reduction_surjective`. -/
  reduction_surjective :
    Function.Surjective (ConcreteSourceEtaleThetaBridge.reduction l)
  /-- `SourceFiniteTheorem311.output_generator_order`. -/
  generator_order :
    addOrderOf (ConcreteSourceEtaleThetaBridge.generator l) = l.value
  /-- `SourceFiniteTheorem311.output_generator_ne_zero`. -/
  generator_ne_zero :
    ConcreteSourceEtaleThetaBridge.generator l ≠ 0
  /-- `SourceFiniteTheorem311.output_root_compatibility`. -/
  root_compatibility :
    ∀ n : ℤ,
      (ConcreteSourceEtaleThetaBridge.packet l).integerRoot n =
        (ConcreteSourceEtaleThetaBridge.roots l).roots (n : ℚ)
  /-- `SourceFiniteTheorem311.output_level_quotient_apply`. -/
  level_quotient_apply :
    ∀ n : ℤ,
      (ConcreteSourceEtaleThetaBridge.algebraicFiniteThetaLevel l).quotientEquiv
          (QuotientAddGroup.mk n) =
        ConcreteSourceEtaleThetaBridge.reduction l n
  /-- `SourceFiniteTheorem311.output_level_quotient_bijective`. -/
  level_quotient_bijective :
    Function.Bijective
      (ConcreteSourceEtaleThetaBridge.algebraicFiniteThetaLevel l).quotientEquiv
  /-- `SourceFiniteTheorem311.output_history_determinant_positive`. -/
  determinant_positive :
    0 < ConcreteSourceHistoryLinkBridge.sourceHistoryDeterminant l
  /-- `SourceFiniteTheorem311.output_history_determinant_log`. -/
  determinant_log :
    Real.log (ConcreteSourceHistoryLinkBridge.sourceHistoryDeterminant l) =
      ConcreteSourceEtaleThetaBridge.thetaLogVolume l

/-- The canonical concrete output satisfies the frozen law bundle.  Every field
is a named theorem already proved over `SourceFiniteOutput.lean`; this theorem
introduces no new mathematical content, only the consumer-facing interface. -/
theorem output_lawBundle (l : PrimeGeFive) : OutputLawBundle l where
  history_terminal_agrees := output_history_terminal l
  history_level_agrees := (output l).history_level_eq_algebraic_level
  history_model_agrees := output_models_agree l
  base_logVolume_eq_thetaLogVolume := procession_base_log_volume l
  history_packet_volume := output_history_packet_volume l
  logVolume_formula := procession_log_volume_is_source_profile l
  logVolume_ind1_invariant := procession_ind1_invariant l
  logVolume_ind2_invariant := procession_ind2_invariant l
  logVolume_ind3_upper := procession_ind3_upper l
  possibleImage_nonempty := procession_possible_nonempty l
  possibleImage_ind1 := procession_possible_ind1 l
  possibleImage_ind2 := procession_possible_ind2 l
  possibleImage_ind3_upper := procession_possible_ind3_upper l
  quotient_same_level := fun hlevel =>
    procession_generated_quotient_same_level hlevel
  quotient_level_separation := fun hlevel =>
    procession_generated_quotient_no_level_collapse hlevel
  quotient_image_nonempty := procession_quotient_image_nonempty l
  quotient_image_ind3_upper := fun a n z hz =>
    procession_quotient_ind3_upper a n z hz
  reduction_kernel := output_reduction_kernel l
  reduction_surjective := output_reduction_surjective l
  generator_order := output_generator_order l
  generator_ne_zero := output_generator_ne_zero l
  root_compatibility := output_root_compatibility l
  level_quotient_apply := output_level_quotient_apply l
  level_quotient_bijective := output_level_quotient_bijective l
  determinant_positive := output_history_determinant_positive l
  determinant_log := output_history_determinant_log l

end SourceFiniteTheorem311

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the finite Q(i)-at-5 discharge of the output law interface
(item 17 output side).  Proved for the single concrete carrier only; the
general source instantiation is the card below. -/
def finiteSourceOutputLawBundle : Obligation :=
  { id := "IUT-III.concrete-source-output-law-bundle"
    source := "IUT III, Theorem 3.11, (i)-(iii) (finite Q(i)-at-5 carrier)"
    status := VerificationStatus.testCarrier
    note :=
      "The frozen field-level law bundle `SourceFiniteTheorem311.OutputLawBundle` " ++
        "groups the output invariants and compatibility laws of the concrete " ++
        "Q(i)-at-5 output (`SourceFiniteTheorem311.output l`): three-part " ++
        "alignment, log-volume normalization anchors and profile formula, " ++
        "Ind1/Ind2 invariance and Ind3 upper-semi laws for log-volume and " ++
        "possible images, quotient same-level/level-separation/nonempty/Ind3-upper " ++
        "laws, and the algebraic-theta laws (reduction kernel and surjectivity, " ++
        "generator order and nonvanishing, root compatibility, level-quotient " ++
        "apply and bijectivity, determinant positivity and logarithm).  " ++
        "`output_lawBundle` proves the bundle; every field is a named theorem " ++
        "already proved over the concrete carrier.  This is the finite-carrier " ++
        "instance of the source-level output law interface; it is not the " ++
        "general source output (see `theorem311SourceInputResidual`)."
    dependsOn :=
      [ "IUT-III.concrete-source-theorem311-output",
        "IUT-III.concrete-source-multiradial-kernel" ] }

/-- Residual card for the output body of `IUT-III.theorem-3.11-output`
(`Theorem311/Obligations.lean:5`): instantiate `Theorem311Source.Input` from the
actual IUT I-II data.

Object: `I : Theorem311Source.Input Label Choice` (the derived-prerequisite
package, `SourceFaithfulBoundary.lean:315`) over the actual source label/choice
data of a procession of D-prime-strips.

Best accepted route: `SourceTheorem311Realization` (`SourceHodgeTheaterBridge.lean:910-919`)
with `R.input` (`:928-952`), whose fields are `SourceLGPProcession`,
`SourcePacketRealization`, `SourceVerticalRealization`, `SourceEvaluationBridge`,
`TheaterFamily`, and a positive labelled count; each field is a cited IUT I-II
construction.

Why blocked: no declaration in the tree constructs those fields from the
opening boundary `OriginalInput` (`SourceOriginalInput.lean:41`).  The vertical
field needs the log-shell/Kummer ([AbsTopIII]-side) content: the bridge card
`SourceLogShellAbsTopIIIBridge` (`IUTII/Kummer/SourceLogShellAbsTopIIIBridge.lean:67,330`)
is a reduced form and does not supply the identification.  Historical
note (preserved): at the time of writing the K1K2 installation was not
accepted and must not have been referenced; this assessment is superseded by
the revision paragraph below.  `SourceTheorem311Completion`
(`SourceRealizationLifting.lean:43-57`) takes `input : Input` as a field, so it
consumes the package rather than constructing it; the finite Q(i)-at-5 world
has no map into `SourceLGPProcession`-style source data.

Revision (2026-10-16, post-K1K2 acceptance): the K1/K2 realization
(`SourceK1K2Realization.lean`) is accepted and derives the three
packet-consistency cards from the log-shell ray presentation; accordingly the
vertical slot is now a conditional construction and the residual reduces to
the procession `P`, the packet `Q`, and the three packet-consistency cards
(`SourceFiniteOutputLawBundleVerticalWiring.lean`; audit record
`theorem311SourceInputResidualReduction`).

Quantifiers: `∀ (l) (Label) (Choice) [AddGroup Label] [Preorder Choice]` over
the paper's actual initial Theta-data and collection of distinct Hodge theaters
(IUT III, Theorem 3.11 opening, III:9151-9163).  Consequence: the general
output remains conditional (`sourceMultiradialOutputDischarge`); the finite
carrier is discharged unconditionally at its own level. -/
def theorem311SourceInputResidual : Obligation :=
  { id := "IUT-III.theorem-3.11-output.source-input-residual"
    source := "IUT III, Theorem 3.11, opening data (III:9151-9163)"
    status := VerificationStatus.interface
    note :=
      "PARK (source input). Object: Theorem311Source.Input over actual source " ++
        "data. Accepted route: SourceTheorem311Realization (SourceHodgeTheaterBridge " ++
        ":910) -> R.input (:928). Blocked: no tree declaration builds its " ++
        "{procession, packet, vertical, evaluation, family} fields from " ++
        "OriginalInput (SourceOriginalInput:41); vertical needs AbsTopIII " ++
        "log-shell/Kummer content (SourceLogShellAbsTopIIIBridge is a reduced " ++
        "form card); K1K2 not accepted (no import); SourceTheorem311Completion " ++
        "consumes Input instead of constructing it. Quantifiers: forall l " ++
        "Label Choice with AddGroup/Preorder. Failed routes: (a) finite carrier " ++
        "instantiation (no map to source-world types); (b) via Completion " ++
        "(circular); (c) via Kummer material (reduced form only). Revision " ++
        "2026-10-16 (supersedes the vertical/K1K2 sentence): the accepted " ++
        "K1K2 realization derives the three packet-consistency cards from " ++
        "the log-shell ray presentation; vertical is a conditional " ++
        "construction (SourceFiniteOutputLawBundleVerticalWiring); the " ++
        "residual is procession + packet + the three cards."
    dependsOn :=
      [ "IUT-I.initial-theta-data",
        "IUT-I-II.prime-strips-frobenioids",
        "IUT-II.vertical-log-kummer",
        "IUT-III.theorem-3.11-output.reduction" ] }

end LeanFormal.IUT.Audit
