# Paper source semantics audit: SourceDefinition31Data

Date: 2026-10-24
Auditor: transport
Scope: semantic audit only. No Lean edits, no new wrapper.
Target: SourceDefinition31Data (LeanFormal.IUT.Theorem311Source.SourceDefinition31Boundary).
Paper object: IUT I Definition 3.1 initial Theta-data, plus the source clauses
(a)-(f) recorded in the same file.

## Verdict up front

SourceDefinition31Data is a CONTRACT SHELL, not a construction of the paper's
initial Theta-data. Only the arithmetic field is made of actual Mathlib
objects. The selected/bad place carriers are bare types; reduction, torsion,
orbicurve, sections, cusp and the five compatibility slots are shell fields
whose propositional or type-valued contents can be inhabited by degenerate
data. Inhabiting those fields with True/PUnit/trivial groups/arbitrary Reals
would be fake source semantics.

The paper-faithful target must replace or explicitly source-qualify those
fields. It must not report SourceDefinition31Data as actual paper data merely
because the structure is inhabited.

## Field-by-field audit

Legend:
- ACTUAL: field content is an actual mathematical object of the corresponding
  paper shape; source existence/compatibility may still be an input.
- UNDERDEFINED: field is a shell/bare type/arbitrary Prop; inhabitation alone
  is not paper content.
- REPLACE: must be replaced or connected to an actual source object/source card
  before paper use.

### arithmetic : InitialThetaArithmeticData l

Paper counterpart: prime l, number fields F_mod / F / K, the Galois tower and
the once-punctured elliptic curve X_F (Definition 3.1 arithmetic input).

Current Lean: actual fields Fmod/F/K with Field/NumberField/Algebra/
IsScalarTower/FiniteDimensional/IsGalois instances; tower : ThetaFieldTower;
curve : PuncturedEllipticCurve F.

Status: ACTUAL OBJECT SHAPE, acceptable as source input.
Caveat: existence of such an arithmetic root and the source conditions linking
the curve to the rest of the Theta-data are not proved. This field is the one
part that is not a fake Prop/Type shell.

### selectedPlaces : Type u

Paper counterpart: the selected place set V of K inducing a section
V -> V_mod of the restriction map (Definition 3.1(e)).

Current Lean: a bare Type with no map to NumberFieldPlace K, no membership
predicate, no finiteness and no relation to arithmetic.K.

Status: UNDERDEFINED / REPLACE.
Bare Type is not the paper V. It can be Empty, PUnit, or any type. The later
SourcePlacePartition structure adds labels and a bad inclusion, but it still
does not make this carrier the actual place set of K.

Required: replace by an actual subtype/set of NumberFieldPlace K (or an actual
canonical section layer) together with the restriction map and the chosen
bad places.

### badPlaces : Type u

Paper counterpart: the bad finite place set V^bad_mod of F_mod, plus labels and
reduction data at those places.

Current Lean: a bare Type, with badFinite/partition supplied only inside
SourceReductionClause.

Status: UNDERDEFINED / REPLACE.
A bare type is not a finite set of finite places of F_mod. It can be inhabited
by PUnit, and the later reduction data can be chosen vacuously/degenerately.

Required: replace by a finite subtype of NumberField.FinitePlace Fmod (or an
actual source card V_mod_bad.Finite), and tie labels to the arithmetic root.

### reduction : SourceReductionClause selectedPlaces badPlaces

Paper counterpart: stable/multiplicative/split-multiplicative reduction at the
bad places and the q-parameter data attached to the initial Theta-data.

Current Lean fields:
- partition : SourcePlacePartition (bare carriers);
- stableReduction / multiplicativeReduction / splitMultiplicativeReduction :
  Bad -> Prop, each with a proof for ALL b;
- qParameter : Bad -> Real, with nonzero, norm < 1 and compatibility proofs;
- reductionCompatibility : split => multiplicative.

Status: UNDERDEFINED / REPLACE.
Every reduction predicate is an arbitrary Prop function proved true for all b;
qParameter is an arbitrary Real function with easy witnesses (for example
q = 1/2). This is a signature shell, not the paper's reduction or q data.
No field ties qParameter to the native Tate/completion q or to the actual
curve at the lifted place.

Required: actual curve reduction predicates at actual places, an actual q
parameter from the initial Theta-data, and a tie to the arithmetic curve. If
these are supplied as source cards, they must be explicit and named; the bare
Prop shell must not be counted as construction.

### torsion : SourceTorsionClause l

Paper counterpart: the six-torsion/l-torsion data and the representation /
Galois-image conditions (Definition 3.1 torsion clause).

Current Lean fields: arbitrary torsionCarrier/representationCarrier/
representationGroup with Group instances, a label to Fin 6, a surjective
representation, and three arbitrary Props (imageContainsSL2,
sixTorsionIndependent, lTorsionCompatible) each with a proof.

Status: UNDERDEFINED / REPLACE.
The groups can be trivial, the representation can be the identity on a trivial
group, and the three Props can be True. This does not encode the actual torsion
of the elliptic curve, its Galois action or the six independent sections.

Required: actual torsion/Galois representation data of the arithmetic curve,
or an explicit actual source card. The trivial group/True shell must not be
used as source content.

### orbicurve : SourceOrbicurveClause

Paper counterpart: hyperbolic orbicurves X_K, C_K, their finite-etale coverings,
the exact sequence of etale fundamental groups, cusp count and curve
compatibility (Definition 3.1(d)).

Current Lean fields: bare Type carriers (curve, puncturedCurve, cover,
structureGroup), arbitrary maps, an exact-sequence clause of bare groups, a
Nat cuspCount, and an arbitrary curveCompatibility Prop with proof.

Status: UNDERDEFINED / REPLACE (strongly).
The clause is explicitly a signature shell. SourceDefinition31OrbicurveInstance
states that no SourceOrbicurveClause is manufactured from the degenerate
terminal etale stack; the fields can still be inhabited by PUnit/trivial
groups. A trivial group exact sequence satisfies the shell but is not a
hyperbolic orbicurve.

Required: actual hyperbolic orbicurves X_K/C_K, the etale fundamental group
data, the finite-etale cover/exact sequence and a geometric genus/puncture
certificate. Until then this field is not paper source content.

### sections : SourceSectionClause

Paper counterpart: the place section V -> V_mod and the local groups of X_K
inside C_K at the selected places, with finite/infinite place data
(Definition 3.1(e)).

Current Lean fields: bare valuationCarrier/modifiedValuationCarrier types,
arbitrary localGroupCarrier functions, arbitrary section maps with two inverse
laws, pointwise bijective localGroupSection, and arbitrary finitePlaceData/
infinitePlaceData Props with proofs.

Status: PARTIAL ACTUAL OUTSIDE THIS FIELD + UNDERDEFINED HERE.
The place-section half D7a is actually constructed in
SourceDefinition31LocalValuationSections (canonical place section layer). That
construction is not this arbitrary SourceSectionClause. D7b (local-group
carriers and pointwise bijections) is still a named supply and needs the actual
orbicurves.

Required: replace the field by the canonical D7a layer plus an actual
D7LocalGroupSectionSupply. The bare localGroupCarrier functions are not source
groups and must not be inhabited arbitrarily.

### cusp : SourceCuspClause

Paper counterpart: the selected cusp and its local normalizations / boundary
cusp epsilon (Definition 3.1(f)).

Current Lean fields: epsilon : Real with 0 < epsilon and != 0; an arbitrary
epsilon_compatibility Prop with proof; cuspScale : Real positive; and a
nonzero-product relation.

Status: UNDERDEFINED / REPLACE.
epsilon = 1, cuspScale = 1 and compatibility = True inhabits the shell. This
is not the paper's selected cusp datum, canonical generator or sign ambiguity.

Required: actual cusp datum from the curve/orbicurve (nonzero quotient,
canonical generator, sign ambiguity) and the Real epsilon/cuspScale source
normalization. If supplied as a source card, it must be actual and named.

### compatibility fields (five pairs)

Fields:
- arithmetic_reduction_compatibility : Prop + proof;
- arithmetic_torsion_compatibility : Prop + proof;
- arithmetic_orbicurve_compatibility : Prop + proof;
- arithmetic_section_compatibility : Prop + proof;
- arithmetic_cusp_compatibility : Prop + proof.

Paper counterpart: the compatibility assertions linking arithmetic and each
source clause (Definition 3.1(a)-(f)).

Status: UNDERDEFINED / REPLACE.
Each is an arbitrary Prop with a proof; all five can be True. This is not the
paper's compatibility content and can fake source coherence.

Required: concrete propositions tied to the actual arithmetic, reduction,
torsion, orbicurve, section and cusp objects, or explicit actual source cards
in D9CompatibilitySupply. An arbitrary True must not be counted as a source
compatibility proof.

## Additional structural gaps

1. selectedPlaces/badPlaces are not tied to arithmetic.Fmod/K by any field.
2. There is no finite/decidable place structure at the top level; badFiniteness
   appears only as a source card inside reduction or as D4D9Supply input.
3. No field identifies a place/label with the actual reduction/torsion data;
   the partition labels are independent of the arithmetic curve.
4. The five compatibility Props are not connected to the clause contents.
5. SourceDefinition31Data can be inhabited by replacing every shell clause with
   degenerate groups/True/constant functions. Such an inhabitant is fake source
   semantics even if Lean accepts it.

## Acceptability summary

| field | paper counterpart | status | acceptable as paper source? | replacement |
|---|---|---|---|---|
| arithmetic | p, F_mod/F/K, tower, X_F | actual object shape | yes, as source input; existence/links not proved | no, preserve and add source links |
| selectedPlaces | V | bare Type | no | actual place subtype/set + restriction map |
| badPlaces | V^bad_mod | bare Type | no | finite place subtype + labels |
| reduction | stable/mult/split + q | arbitrary Prop/Real shell | no | actual reduction/q data or explicit source cards |
| torsion | six/l-torsion + Galois rep | arbitrary group shell | no | actual torsion/Galois data or source card |
| orbicurve | X_K/C_K + fundamental groups | arbitrary Type/group shell; degenerate possible | no | actual hyperbolic orbicurve/fundamental groups |
| sections | V->V_mod + local groups | D7a actual elsewhere; field is shell | no (field itself) | canonical D7a layer + actual D7b supply |
| cusp | selected cusp/epsilon | arbitrary Real/Prop shell | no | actual cusp datum + epsilon source card |
| five compatibility | arithmetic-source compatibility | arbitrary Prop/proof | no | concrete source propositions/source cards |

## Required policy

- Do not report SourceDefinition31Data as actual paper source data.
- Do not fill shell clauses with True/PUnit/trivial groups/constant Reals and
  call the result source semantics.
- Preserve arithmetic as the actual arithmetic source input; do not re-derive
  its existence from arbitrary data.
- Replace or explicitly source-qualify the other fields with actual paper
  objects/cards.
- Keep the distinction between:
  (a) actual arithmetic root and curve;
  (b) actual D7a canonical place-section layer;
  (c) source cards that are still missing (V_mod_bad finite, reduction/q,
      torsion, orbicurve, D7b local groups, cusp, five compatibilities).
- No new wrapper around SourceDefinition31Data is a substitute for replacing
  these fields.

## Status

- statement audit: source-level only; no Lean build run.
- target_accepted: false.
- Main finding: only arithmetic is actual; the other fields are underdefined
  shells or arbitrary Props and must be replaced or explicitly sourced.
