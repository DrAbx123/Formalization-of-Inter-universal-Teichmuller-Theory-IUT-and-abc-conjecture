import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ContractSourceReduction
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# The 1,∘ arithmetic holomorphic structure and the SHE localization landing (reduced interface)

This module freezes the reduced source-level interface of the "arithmetic holomorphic
structure in the 1-column" of IUT III, Corollary 3.12, Step (xi-c) -- "in essence, the
ring structure labeled 1,∘" -- together with the reduced form of the predicate that the
output data of the multiradial construction algorithm of Theorem 3.11 is expressed in
terms of localizations of arithmetic vector bundles over the local rings labeled "1,∘"
(the landing point of the SHE property, cf. DSH-F report §API-5).

## Original (paper) route

* IUT III, Corollary 3.12, Step (xi-c) (focused extract `:1045-1066`, PDF p. 182): the
  algorithm of Theorem 3.11 yields a collection of possibilities of output data in `1,∘U`
  linked/related [cf. (IPL)], via isomorphisms of F-prime-strips, to the representation
  [via the log-Kummer correspondence in the 1-column] of the q-pilot object at (1,0) on
  `1,∘U_Q`, and whose construction "may be expressed entirely relative to the arithmetic
  holomorphic structure in the 1-column" [cf. (SHE)].  This structure "amounts, in
  essence, to the ring structure labeled 1,∘".  After enlarging by the holomorphic hull
  `1,∘U ⊇ 1,∘U`, the output data is expressed -- not in terms of regions contained in
  tensor products of local fields labeled 1,∘ [isomorphs of `K_v`] -- but "in terms of
  localizations of arithmetic vector bundles over certain local rings labeled 1,∘" [i.e.,
  isomorphs of `O_{K_v}`, for v in V]; this is necessary to render the output data
  comparable to the representation of the q-pilot object [a certain arithmetic line
  bundle] at (1,0) on `1,∘U_Q`.
* IUT III, Corollary 3.12, Step (xi-d) (`:1070-1110`): the localizations of arithmetic
  vector bundles are of rank > 1, unlike the arithmetic line bundle giving rise to the
  q-pilot object; comparability is obtained only through determinants and the log-volume;
  the log-Kummer correspondence in the 1-column rectifies the vertical shift.
* IUT III, Corollary 3.12, Step (xi-e) (`:1111-1135`): "expressibility relative to the
  arithmetic holomorphic structure in the 1-column" amounts precisely to expressibility
  via operations valid/executable/well-defined even under the condition that the
  pilot-object log-volume attached to the input data prime-strip be the fixed value
  `-|log(q)|`.
* IUT III, Remark 3.11.1, (iii) (SHE) (pagewise plain text `:9890-9907`, PDF p. 161): the
  construction of the output data, as well as the output data itself, is expressed in
  terms simultaneously valid/executable/well-defined relative to both the arithmetic
  holomorphic structure of the Θ-link domain and that of the Θ-link codomain.
* The paper`s referenced discussion of the localizations of arithmetic vector bundles is
  Remark 3.9.5, (vii), (Ob1), (Ob2), (Ob5); Remark 3.12.2, (v).

## Reduced route (deviations)

R1. Binding. The 1-column itself and any identification of the frozen record with a
    structure labeled "1,∘" or with a source column (`fPrimeStripAt`) are NOT
    constructed; the structure is an abstract record indexed by the place type.  The
    binding of `HodgeTheater.arithmetic`-style carriers to the label "1,∘" remains open
    (DSH-F §API-5, gap S3).
R2. Fiber data. `localRing`/`localField` and the localization inclusions are abstract
    carriers; the actual number fields, valuations, completions and integral structures
    are not constructed for the V-parametrized interface.  Section 6 constructs the
    fiber data for `V = NumberField.FinitePlace k` from the completed carrier `K_v`
    and its valuation ring `O_v` (`Foundations/NumberField`).
R3. Bundle. `SourceArithmeticVectorBundle` carries only a section carrier and per-place
    localization readings; the module/sheaf structure, rank, integrality, and the
    Frobenioid-theoretic arithmetic structure are not modeled.  Carriers of this reduced
    interface live at universe 0 (`Type`), matching the convention of the surrounding
    strip/unit-quotient carriers; universe lifting is postponed.
R4. Expression. "Expressed in terms of" is reduced to: the output datum carries a reading
    map into the 1,∘ local rings, and every reading factors through the bundle`s
    localization map (`isLocalizationReading`).  The positive content that the readings
    are localizations over the local rings (rather than regions in tensor products of
    local fields) is carried only through the `localRing`/`localField` split; no formal
    negative statement is frozen, and the operation-level reading of SHE ((xi-e)) is not
    modeled.
R5. Link clause. The (IPL)-half of (xi-c)/(xi-d) (the isomorphisms of F-prime-strips to
    the log-Kummer representation of the q-pilot object on `1,∘U_Q`) is NOT restated
    here; the log-Kummer correspondence and the q-pilot identification remain named gaps
    (DSH-F §API-7 chain).
R6. Hull and log-volume. The holomorphic hull enlargement `1,∘U ⊇ 1,∘U`, determinants and
    the log-volume comparison (Step (xi-d)-(xi-f)) are out of scope of this module.

## Named source cards (not constructed here)

* Card AS: `SourceOneColumnArithmeticHolomorphicStructure` (per-place local rings
  O_{K_v} with their commutative ring structure, local fields `K_v`, localization
  inclusions).
* Card AV: `SourceArithmeticVectorBundle` (section carrier with per-place localization
  readings).
* Card SL: `SourceLocalizationExpression` and the predicate `SourceLocalizationExpressible`
  (the SHE landing statement surface).

## Proved here

The localization-inclusion laws; gate-only satisfiability witnesses for Cards AS and AV;
the assembling construction; the existence characterization (gate) for Card SL; the
characterization of the landing predicate; transport of expressibility along equivalences
of the output carrier; the (SHE)-slot assembly record and the landing-evidence transport
into the north-wall contract slot (Section 4); the two instantiation-site assemblies,
conditional on the named SHE-landing card (Section 5); the number-field completion
instance of Card AS and the explicit landing statement over it (Sections 6-7).

## Not claimed here

The actual 1-column structure, its binding to the label "1,∘" or to any column, the
actual arithmetic vector bundles and their localizations, the log-Kummer representation
of the q-pilot object, the holomorphic hull, the operation-level reading of SHE, and any
IPL/SHE/APT conclusion.

## Consumers

* The (SHE) slot of the north-wall three-card contract: `StepXIContract.she`
  (`Corollary312/StepXI/Contract.lean:38`; evidence field `she_evidence` at
  Contract.lean:41; obligation dependency `IUT-III.SHE` at Contract.lean:75).
  Instantiation points `ContractSourceReduction.lean:212-213` and `:270-271`
  (`finiteLinkEvidenceOfHullTarget` / `StepXIContract.ofAbsoluteDegreeNormalizedSignedLog`,
  arguments `she`/`she_evidence`); parametric carrier `ParametricStepXI.lean:36`/`:39`.
  See Section 4 for the assembly record `SourceSHELandingSlotAssembly` and the
  landing-evidence transport `sheSlot_evidence`.
* The Step (xi-d)/(xi-e) chains: determinant/log-volume comparisons consume the
  local-ring and bundle layers; the fixed `-|log(q)|` reading consumes the pilot-volume
  layer (separate hull/log-volume contract).
* This module deliberately does NOT consume the TA/U2P data surfaces of
  `SourceMultiradialTwoActionEquivalence.lean`; no two-action data is used or restated.

## Paper locations

Corollary 3.12, Step (xi-c): focused extract
`text\source_audit\IUTIII_Theorem311_pp153-159_Corollary312_pp173-186.plain.txt:1045-1066`
(PDF physical p. 182); Step (xi-d): 1070-1110; Step (xi-e): 1111-1135.  Remark 3.11.1,
(iii) (SHE): pagewise plain text 9890-9907 (PDF p. 161).  Remark 3.9.5, (vii), (Ob1),
(Ob2), (Ob5); Remark 3.12.2, (v).  DSH-F report:
`tmp\dsh-card-ipl-she-apt-20261016\REPORT.md`, §API-5 (line 548 seqq.), §2.2 (S1-S5),
§1.3 (Step (xi) table).
-/

namespace LeanFormal.IUT

universe uv uOut

namespace Theorem311Source

/-! ## 1. Card AS: the arithmetic holomorphic structure in the 1-column -/

/-- Card AS: the (reduced) arithmetic holomorphic structure in the 1-column -- "in
essence, the ring structure labeled 1,∘" (Step (xi-c)).

Original: the ring/scheme structure labeled "1,∘" of the first column of the log-theta-
lattice, whose localizations of arithmetic vector bundles are isomorphs of `O_{K_v}`
(against the local fields `K_v`).  Reduced form: per-place local rings and local fields
with their ring/field structures and the localization inclusions are carried as data;
no binding to the 1-column or to the label "1,∘" is constructed (R1, R2).

Consumers: the (SHE) slot of the north-wall three-card contract; the Step (xi-d)/(xi-e)
determinant/log-volume chains. -/
structure SourceOneColumnArithmeticHolomorphicStructure (V : Type uv) where
  /-- the local rings `O_{K_v}`, labeled 1,∘, in which the localizations of arithmetic
  vector bundles are read -/
  localRing : V → Type
  /-- the commutative ring structure carried by each local ring -/
  ringOf : ∀ v : V, CommRing (localRing v)
  /-- the local fields `K_v`, labeled 1,∘ (the regions the output data must not merely
  be expressed by, cf. Step (xi-c)) -/
  localField : V → Type
  /-- the field structure carried by each local field -/
  fieldOf : ∀ v : V, Field (localField v)
  /-- the localization inclusion `O_{K_v} → K_v` at every place -/
  localizationInclusion : ∀ v : V, localRing v →+* localField v

attribute [instance] SourceOneColumnArithmeticHolomorphicStructure.ringOf
attribute [instance] SourceOneColumnArithmeticHolomorphicStructure.fieldOf

namespace SourceOneColumnArithmeticHolomorphicStructure

/-- The localization inclusion is unital. -/
theorem localizationInclusion_one {V : Type uv}
    (S : SourceOneColumnArithmeticHolomorphicStructure V) (v : V) :
    S.localizationInclusion v 1 = 1 :=
  (S.localizationInclusion v).map_one

/-- The localization inclusion is multiplicative. -/
theorem localizationInclusion_mul {V : Type uv}
    (S : SourceOneColumnArithmeticHolomorphicStructure V) (v : V)
    (x y : S.localRing v) :
    S.localizationInclusion v (x * y) =
      S.localizationInclusion v x * S.localizationInclusion v y :=
  (S.localizationInclusion v).map_mul x y

/-- Gate-only witness: the frozen record is satisfiable (local rings `ℤ`, local fields
`ℚ`, the cast `ℤ →+* ℚ`).  Contains no arithmetic content and is not a construction of
the paper`s 1,∘ structure or of any number field. -/
theorem nonempty (V : Type uv) :
    Nonempty (SourceOneColumnArithmeticHolomorphicStructure V) :=
  ⟨{ localRing := fun _ => ℤ
     ringOf := fun _ => inferInstance
     localField := fun _ => ℚ
     fieldOf := fun _ => inferInstance
     localizationInclusion := fun _ => Int.castRingHom ℚ }⟩

end SourceOneColumnArithmeticHolomorphicStructure

/-! ## 2. Card AV: arithmetic vector bundles over the 1,∘ rings -/

/-- Card AV: a (reduced) arithmetic vector bundle over the 1,∘ local rings, with its
localizations.

Original: the "localizations of arithmetic vector bundles over certain local rings
labeled 1,∘" (isomorphs of `O_{K_v}`) of Step (xi-c).  Reduced form: a section carrier
and a per-place localization reading into the local rings; the module/sheaf structure,
rank and integrality are not modeled (R3). -/
structure SourceArithmeticVectorBundle {V : Type uv}
    (S : SourceOneColumnArithmeticHolomorphicStructure V) where
  /-- the carrier of sections of the bundle -/
  total : Type
  /-- the localization of a section at every place, read in the 1,∘ local ring -/
  localization : ∀ v : V, total → S.localRing v

namespace SourceArithmeticVectorBundle

/-- Gate-only witness: the zero bundle (one-point section carrier, zero readings) is
satisfiable.  Contains no arithmetic content and is not the paper`s bundle. -/
theorem nonempty {V : Type uv} (S : SourceOneColumnArithmeticHolomorphicStructure V) :
    Nonempty (SourceArithmeticVectorBundle S) :=
  ⟨{ total := PUnit
     localization := fun _ _ => 0 }⟩

end SourceArithmeticVectorBundle

/-! ## 3. Card SL: the SHE localization landing -/

/-- Card SL: the (reduced) localization expression of output data: the output data of
the multiradial construction algorithm is expressed in terms of localizations of an
arithmetic vector bundle over the 1,∘ local rings.

Original: Step (xi-c): the construction "may be expressed entirely relative to the
arithmetic holomorphic structure in the 1-column"; concretely in terms of localizations
of arithmetic vector bundles.  Reduced form: the output datum plus a reading map into
the 1,∘ local rings, with every reading factoring through the bundle`s localization map
(R4).  The (IPL)-link clause is not restated (R5).

Consumers: the (SHE) slot of the north-wall three-card contract (Step (xi-b)/(xi-c));
`sourceLocalizationExpressible_of_equiv` is the transport form consumed together with
output equivalences. -/
structure SourceLocalizationExpression {V : Type uv}
    (S : SourceOneColumnArithmeticHolomorphicStructure V) (Output : Type uOut) where
  /-- the arithmetic vector bundle over the 1,∘ local rings whose localizations the
  output data are expressed by -/
  bundle : SourceArithmeticVectorBundle S
  /-- the constructed output datum (a possibility of Theorem 3.11 output data) -/
  output : Output
  /-- the expression: the reading of the output datum in the 1,∘ local ring at every
  place -/
  expression : ∀ v : V, Output → S.localRing v
  /-- the (reduced) localization-reading condition: every reading factors through the
  bundle`s localization map, so that the expression is in terms of localizations of
  the arithmetic vector bundle and not an ad hoc family of maps -/
  isLocalizationReading : ∀ (v : V) (o : Output),
    ∃ s : bundle.total, expression v o = bundle.localization v s

namespace SourceLocalizationExpression

/-- Assembly of the reduced localization expression from an output datum (zero bundle,
zero reading, factorized).  Gate-only: contains no arithmetic content. -/
def sourceLocalizationExpressionOf {V : Type uv}
    (S : SourceOneColumnArithmeticHolomorphicStructure V) (Output : Type uOut)
    (o : Output) : SourceLocalizationExpression S Output where
  bundle :=
    { total := PUnit
      localization := fun _ _ => 0 }
  output := o
  expression := fun _ _ => 0
  isLocalizationReading := fun _ _ => ⟨PUnit.unit, rfl⟩

/-- Gate/characterization: a localization expression exists exactly when the output
carrier is nonempty. -/
theorem nonempty_iff {V : Type uv} (S : SourceOneColumnArithmeticHolomorphicStructure V)
    (Output : Type uOut) :
    Nonempty (SourceLocalizationExpression S Output) ↔ Nonempty Output :=
  ⟨fun ⟨E⟩ => ⟨E.output⟩,
    fun ⟨o⟩ => ⟨sourceLocalizationExpressionOf S Output o⟩⟩

end SourceLocalizationExpression

/-- The SHE localization landing predicate (reduced; the predicate requested by DSH-F
§API-5): the output data has an expression in terms of localizations of an arithmetic
vector bundle over the 1,∘ local rings.

Consumers: the (SHE) slot of the north-wall three-card contract -- `StepXIContract.she`
at `Corollary312/StepXI/Contract.lean:38` with evidence field `she_evidence : she` at
Contract.lean:41 (obligation dependency `IUT-III.SHE` at Contract.lean:75).  The
assembly record `SourceSHELandingSlotAssembly` and the transport `sheSlot_evidence`
are in Section 4 below. -/
def SourceLocalizationExpressible {V : Type uv}
    (S : SourceOneColumnArithmeticHolomorphicStructure V) (Output : Type uOut) : Prop :=
  Nonempty (SourceLocalizationExpression S Output)

/-- Gate/characterization for the landing predicate. -/
theorem sourceLocalizationExpressible_iff {V : Type uv}
    (S : SourceOneColumnArithmeticHolomorphicStructure V) (Output : Type uOut) :
    SourceLocalizationExpressible S Output ↔ Nonempty Output :=
  SourceLocalizationExpression.nonempty_iff S Output

/-- Transport: expressibility of output data transports along equivalences of the output
carrier.  This is the form in which the landing predicate is consumed together with
output comparisons (e.g. an output equivalence between two instances). -/
theorem sourceLocalizationExpressible_of_equiv {V : Type uv}
    {S : SourceOneColumnArithmeticHolomorphicStructure V}
    {Output Output' : Type uOut} (e : Output ≃ Output')
    (h : SourceLocalizationExpressible S Output) :
    SourceLocalizationExpressible S Output' := by
  rcases h with ⟨E⟩
  refine ⟨{ bundle := E.bundle
            output := e E.output
            expression := fun v o' => E.expression v (e.symm o')
            isLocalizationReading := ?_ }⟩
  intro v o'
  simpa using E.isLocalizationReading v (e.symm o')

/-! ## 4. (SHE) slot assembly into the north-wall contract -/

/-- Minimal assembly point wiring the API-5 landing predicate into the (SHE) slot of
the north-wall three-card contract (`Corollary312/StepXI/Contract.lean`).

Consumers (file:line): the slot declaration `StepXIContract.she` at
`Contract.lean:38` and its evidence field `she_evidence : she` at `Contract.lean:41`
(the contract-construction obligation lists `IUT-III.SHE` at `Contract.lean:75`);
instantiation sites `ContractSourceReduction.lean:212-213`
(`finiteLinkEvidenceOfHullTarget`, arguments `she`/`she_evidence`) and
`ContractSourceReduction.lean:270-271`
(`StepXIContract.ofAbsoluteDegreeNormalizedSignedLog`, same arguments); parametric
carrier fields `ParametricStepXI.lean:36`/`:39` (`StepXIInput.she`/`she_evidence`).

The contract is NOT constructed here: the signed quantities, the (IPL)/(APT)
propositions with their evidence, and the two real comparisons remain caller
obligations, and no slot is closed by `True` or by any trivial proposition.  Frozen
here is only the identification: the assembled contract carries the API-5 landing
predicate `SourceLocalizationExpressible S Output` in its (SHE) slot, so that a
caller building the contract with `she := SourceLocalizationExpressible S Output`
inhabits `slot_identifies` by `rfl` and obtains the slot evidence from landing
evidence via `sheSlot_evidence`. -/
structure SourceSHELandingSlotAssembly {V : Type uv}
    (S : SourceOneColumnArithmeticHolomorphicStructure V) (Output : Type uOut) where
  /-- the north-wall contract whose (SHE) slot is wired -/
  contract : StepXIContract
  /-- identification of the contract`s (SHE) slot with the API-5 landing predicate
  (definitional for a contract built with `she := SourceLocalizationExpressible S
  Output`; stored as data) -/
  slot_identifies : contract.she = SourceLocalizationExpressible S Output

namespace SourceSHELandingSlotAssembly

/-- Evidence transport into the (SHE) slot: landing evidence for `S` and `Output`
is evidence for the assembled contract`s (SHE) slot.  This is the consumer-facing
form for callers at `ContractSourceReduction.lean:213`/`:271` that pass
`she := SourceLocalizationExpressible S Output`. -/
theorem sheSlot_evidence {V : Type uv}
    {S : SourceOneColumnArithmeticHolomorphicStructure V} {Output : Type uOut}
    (A : SourceSHELandingSlotAssembly S Output)
    (h : SourceLocalizationExpressible S Output) : A.contract.she :=
  Eq.mp A.slot_identifies.symm h

end SourceSHELandingSlotAssembly

/-! ## 5. Instantiation-site assemblies (conditional on the named SHE-landing card) -/

noncomputable section

/-- Conditional assembly at the first instantiation site: `finiteLinkEvidenceOfHullTarget`
(`ContractSourceReduction.lean:210-213`) with the (SHE) slot instantiated by the API-5
landing predicate, followed by `StepXIFiniteCertificate.toContract`
(`FiniteCertificateBridge.lean:29-41`); on the resulting contract the (SHE) slot is
definitionally the landing predicate (`slot_identifies` is `rfl`).

Unconditional closure at this site is not available: supplying `she` with a proof
of it from a gate only would require a trivially closed proposition such as
`Nonempty Output`, which the frozen traps forbid.  The missing source input is
the named card `IUT-III.source-SHE-landing-evidence` (Audit below); this assembly
is conditional on that evidence and asserts nothing about its availability. -/
def SourceSHELandingSlotAssembly.ofHullTargetLink {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label)
    (ipl apt : Prop) (ipl_evidence : ipl) (apt_evidence : apt)
    {V : Type uv} {S : SourceOneColumnArithmeticHolomorphicStructure V}
    {Output : Type uOut} (landing : SourceLocalizationExpressible S Output) :
    SourceSHELandingSlotAssembly S Output where
  contract :=
    certificate.toContract
      (finiteLinkEvidenceOfHullTarget certificate ipl
        (SourceLocalizationExpressible S Output) apt ipl_evidence landing apt_evidence)
  slot_identifies := rfl

/-- Conditional assembly at the second instantiation site:
`StepXIContract.ofAbsoluteDegreeNormalizedSignedLog`
(`ContractSourceReduction.lean:259-271`) with the (SHE) slot instantiated by the API-5
landing predicate and the landing evidence supplied as `landing` (site lines 270-271);
`slot_identifies` is `rfl`.  Same conditional status as `ofHullTargetLink`. -/
def SourceSHELandingSlotAssembly.ofAbsoluteDegreeNormalizedSignedLog
    {k : Type*} [Field k] [NumberField k]
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) ->
      NumberFieldFinitePlace.FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty)
    (targetSigned thetaSigned : Real)
    (q_le_target :
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters <= targetSigned)
    (target_le_theta : targetSigned <= thetaSigned)
    (ipl apt : Prop) (ipl_evidence : ipl) (apt_evidence : apt)
    {V : Type uv} {S : SourceOneColumnArithmeticHolomorphicStructure V}
    {Output : Type uOut} (landing : SourceLocalizationExpressible S Output) :
    SourceSHELandingSlotAssembly S Output where
  contract :=
    StepXIContract.ofAbsoluteDegreeNormalizedSignedLog selectedLowerPlaces parameters
      selected_nonempty targetSigned thetaSigned q_le_target target_le_theta
      ipl (SourceLocalizationExpressible S Output) apt ipl_evidence landing apt_evidence
  slot_identifies := rfl

end

/-! ## 6. A non-gate instance of Card AS from number-field completions -/

noncomputable section

/-- The actual-completion instance of the 1-column arithmetic holomorphic structure:
over the finite places of a number field `k`, the local rings are the completed
valuation rings `O_v` (`NumberFieldFinitePlace.CompletionIntegers`, the adic
completion of the localization of `O_k` at the place) and the local fields are the
adic completions `K_v` (`NumberFieldFinitePlace.Completion`), with the localization
inclusion given by `ValuationSubring.subtype`.

Reused from `Foundations/NumberField/LocalQParameter.lean` (completed carrier; see
also `PlaceCompletionCarrier.lean` for the residue field).  Reductions: the identity
of `O_v`/`K_v` with the paper`s objects labeled 1,∘ is the intended reading but is
NOT asserted, and the binding to a source column remains outside the reduced
interface (R1); carriers live at universe 0 (R3). -/
def sourceOneColumnStructureOfNumberField (k : Type) [Field k] [NumberField k] :
    SourceOneColumnArithmeticHolomorphicStructure (NumberField.FinitePlace k) where
  localRing := fun v => NumberFieldFinitePlace.CompletionIntegers v
  ringOf := fun _ => inferInstance
  localField := fun v => NumberFieldFinitePlace.Completion v
  fieldOf := fun _ => inferInstance
  localizationInclusion := fun v =>
    ValuationSubring.subtype (NumberFieldFinitePlace.CompletionIntegers v)

@[simp] theorem sourceOneColumnStructureOfNumberField_localRing
    (k : Type) [Field k] [NumberField k] (v : NumberField.FinitePlace k) :
    (sourceOneColumnStructureOfNumberField k).localRing v =
      NumberFieldFinitePlace.CompletionIntegers v := rfl

@[simp] theorem sourceOneColumnStructureOfNumberField_localField
    (k : Type) [Field k] [NumberField k] (v : NumberField.FinitePlace k) :
    (sourceOneColumnStructureOfNumberField k).localField v =
      NumberFieldFinitePlace.Completion v := rfl

/-! ## 7. The explicit landing statement over the completion instance -/

/-- The explicit statement of the SHE landing card over the actual completion
carriers: for the 1-column structure built from the finite places of a number field
and any output carrier, the landing predicate holds if and only if there exist a
section carrier, an output datum, and a per-place reading of the output into the
completed valuation rings `O_v` that factors through the bundle localizations at
every place.

This concentrates the remaining content of the card into constructing those data
(`IUT-III.source-SHE-landing-evidence`): an arithmetic vector bundle over the
one-column (a localization-theoretic object over the `O_v`), an output datum, a
reading, and the factorization.  The bundle object itself is the minimal new
mathematics, since no arithmetic-vector-bundle structure exists in this repository. -/
theorem sourceLocalizationExpressible_completions_iff
    (k : Type) [Field k] [NumberField k] (Output : Type uOut) :
    SourceLocalizationExpressible (sourceOneColumnStructureOfNumberField k) Output ↔
      ∃ (B : SourceArithmeticVectorBundle (sourceOneColumnStructureOfNumberField k))
        (o : Output)
        (e : ∀ v : NumberField.FinitePlace k, Output →
          NumberFieldFinitePlace.CompletionIntegers v),
        ∀ (v : NumberField.FinitePlace k) (o' : Output),
          ∃ s : B.total, e v o' = B.localization v s := by
  constructor
  · rintro ⟨E⟩
    exact ⟨E.bundle, E.output, E.expression, E.isLocalizationReading⟩
  · rintro ⟨B, o, e, hfac⟩
    exact ⟨{ bundle := B
             output := o
             expression := e
             isLocalizationReading := hfac }⟩

/-- Hookup of the completion instance into `SourceSHELandingSlotAssembly` at the
second instantiation site (`ContractSourceReduction.lean:270-271`): the conditional
assembly with the 1-column structure instantiated by
`sourceOneColumnStructureOfNumberField k`.  The residual input is the landing
evidence for `Output` -- the unique open card `IUT-III.source-SHE-landing-evidence`
-- and no other slot of this assembly is fabricated. -/
def SourceSHELandingSlotAssembly.ofNumberFieldCompletions
    {k : Type} [Field k] [NumberField k]
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      NumberFieldFinitePlace.FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty)
    (targetSigned thetaSigned : Real)
    (q_le_target :
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters <= targetSigned)
    (target_le_theta : targetSigned <= thetaSigned)
    (ipl apt : Prop) (ipl_evidence : ipl) (apt_evidence : apt)
    {Output : Type uOut}
    (landing : SourceLocalizationExpressible
      (sourceOneColumnStructureOfNumberField k) Output) :
    SourceSHELandingSlotAssembly (sourceOneColumnStructureOfNumberField k) Output :=
  SourceSHELandingSlotAssembly.ofAbsoluteDegreeNormalizedSignedLog
    selectedLowerPlaces parameters selected_nonempty targetSigned thetaSigned
    q_le_target target_le_theta ipl apt ipl_evidence apt_evidence landing

end

end Theorem311Source

namespace Audit

def sourceArithmeticHolomorphicLanding : Obligation :=
  { id := "IUT-III.source-arithmetic-holomorphic-landing"
    source :=
      "IUT III, Corollary 3.12, Step (xi-c) ((xi-d), (xi-e)); Remark 3.11.1, (iii), " ++
        "(SHE); Remark 3.9.5, (vii), (Ob1), (Ob2), (Ob5); Remark 3.12.2, (v)"
    status := VerificationStatus.interface
    note :=
      "Reduced source interface for the arithmetic holomorphic structure in the " ++
        "1-column (in essence the ring structure labeled 1,∘) and for the SHE " ++
        "landing: the predicate that output data is expressed in terms of " ++
        "localizations of arithmetic vector bundles over the 1,∘ local rings. " ++
        "Frozen records: SourceOneColumnArithmeticHolomorphicStructure (per-place " ++
        "local rings O_{K_v} with their commutative ring structure, local fields " ++
        "K_v, localization inclusions), SourceArithmeticVectorBundle (section " ++
        "carrier with per-place localization readings), SourceLocalizationExpression " ++
        "(bundle, output datum, reading map, factorization through the bundle " ++
        "localizations), and the predicate SourceLocalizationExpressible. Proved: " ++
        "localization-inclusion laws, gate witnesses, existence characterizations, " ++
        "the assembler, and transport of expressibility along output equivalences. " ++
        "NOT constructed: the actual 1-column structure or any binding to the label " ++
        "1,∘ or to a source column, the actual arithmetic vector bundles, the " ++
        "log-Kummer representation of the q-pilot object, the holomorphic hull, and " ++
        "the operation-level reading of SHE ((xi-e)); no IPL/SHE/APT conclusion is " ++
        "asserted. (SHE)-slot assembly: SourceSHELandingSlotAssembly (Section 4) " ++
        "identifies a given StepXIContract.she slot with the landing predicate and " ++
        "transports landing evidence into the slot; the contract itself is still " ++
        "not constructed and no slot is closed by True " ++
        "(Corollary312/StepXI/Contract.lean:38-41, 75). Section 6 constructs a " ++
        "non-gate instance over the finite places of a number field (completed " ++
        "valuation rings and adic completions); the remaining SHE content is " ++
        "tracked solely by IUT-III.source-SHE-landing-evidence."
    dependsOn :=
      [ "IUT-III.source-kummer-evaluation-arrows",
        "IUT-III.theorem-3.11-output",
        "IUT-III.StepXI.contract-construction" ] }

/-- Named card for the missing source input at the two instantiation sites: an actual
witness of the SHE landing predicate, consumed as the hypothesis `landing`. -/
def sourceSHELandingEvidenceSupply : Obligation :=
  { id := "IUT-III.source-SHE-landing-evidence"
    source :=
      "IUT III, Corollary 3.12, Step (xi-c) ((xi-d), (xi-e)); Remark 3.11.1, (iii), " ++
        "(SHE)"
    status := VerificationStatus.pending
    note :=
      "Named card: actual source construction of a witness of the SHE landing " ++
        "evidence, i.e. of SourceLocalizationExpressible (the card " ++
        "IUT-III.source-arithmetic-holomorphic-landing), consumed as the " ++
        "hypothesis landing of SourceSHELandingSlotAssembly.ofHullTargetLink (site " ++
        "ContractSourceReduction.lean:212-213) and " ++
        "SourceSHELandingSlotAssembly.ofAbsoluteDegreeNormalizedSignedLog (site " ++
        "ContractSourceReduction.lean:270-271). Constructing it requires the actual " ++
        "1-column structure, the actual arithmetic vector bundles, and the " ++
        "operation-level SHE reading (reductions R1-R5 of this module). NOT " ++
        "constructed here; the two site assemblies are conditional on this evidence. " ++
        "Drill-down (Sections 6-7): with the 1-column coefficient side constructed " ++
        "from number-field completions, this card reduces exactly to the expression " ++
        "datum over those carriers (sourceLocalizationExpressible_completions_iff)."
    dependsOn :=
      [ "IUT-III.source-arithmetic-holomorphic-landing" ] }

end Audit

end LeanFormal.IUT

