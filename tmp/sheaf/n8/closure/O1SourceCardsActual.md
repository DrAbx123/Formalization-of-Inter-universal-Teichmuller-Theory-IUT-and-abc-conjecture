# O1 source cards actual / exact no-go

Date: 2026-10-24
Owner: transport
Scope: only O1 source cards: orbicurve, sections, cusp, compatibility.
No LGP/assembly wrapper. No files modified except this note and the new O1 Lean
file.

## Verdict

None of the four source cards is actually constructed from N8NativeInput.
The decisive no-go is exact: native data supplies neither the required source
objects nor a production constructor/theorem from the native record.

Actual part: the D7a place-section layer is canonical for every arithmetic
input, and SourceSectionClause can be assembled conditionally from the D7b
local-group supply via the production d7SectionLayerBridge.  The D7b supply is
itself the exact gap.

## Card-by-card status

### 1. Orbicurve

Target: SourceOrbicurveClause.

Required source object content:
- actual hyperbolic orbicurves X_K and C_K over K, with the K-core relation;
- the finite etale covering data and the exact sequence of etale fundamental
  groups;
- certified arithmetic/geometric etale fundamental group data;
- the cusp count and curve compatibility.

Status: EXACT GAP, no native constructor.

Production evidence:
- SourceDefinition31OrbicurveInstance.lean explicitly refuses to manufacture
  SourceOrbicurveClause from the terminal/degenerate etale stack; the terminal
  stack is not hyperbolic and carries no orbicurve geometry.
- SourceDefinition31D4D9Supply.lean records the orbicurve slot as an explicit
  source supply; D6 gate is open.
- SourceClauseConstructors.ofFundamentalGroup requires an actual
  HyperbolicOrbicurve plus certified etale fundamental groups; no compiled
  supplier from InitialThetaArithmeticData or N8NativeInput.

Missing source theorem/object: D6OrbicurveConstruction at the actual
hyperbolic-orbicurve carrier, not a clause shell.

### 2. Sections

Target: SourceSectionClause.

Status: PARTIAL ACTUAL + EXACT GAP.
- D7a (place-section half) is ACTUAL for every arithmetic input:
  SourceValuationSectionLayer.canonical constructs the selected-place carrier,
  the restriction map, the section, and both inverse laws.
- D7b (local-group half) is the exact gap: localGroupCarrier and
  modifiedLocalGroupCarrier over the section carrier pair, pointwise bijective
  localGroupSection, and finite/infinite place data.
- Given D7LocalGroupSectionSupply, the full SourceSectionClause is ACTUAL via
  production d7SectionLayerBridge (conditional constructor, implemented in the
  Lean file).
- The D7b supply needs the actual orbicurves X_K, C_K and their local/etale
  fundamental groups (D6); native S does not contain them.
- The 16-slot clause is not produced unconditionally; D7a alone leaves the
  local-group and place-data slots empty.

Missing source theorem/object: D7bLocalGroupSectionConstruction /
D7LocalGroupSectionSupply for the canonical place-section layer.

### 3. Cusp

Target: SourceCuspClause.

Required source object content:
- selected cusp datum over the epsilon carrier: nonzero quotient, canonical
  generator, sign ambiguity (all with proofs);
- the Real epsilon and cuspScale source card, positivity and nonzero relation;
- the cusp epsilon compatibility proposition and proof.

Status: EXACT GAP, no native constructor.

Production evidence:
- D8 records the cusp origin from the nonzero quotient element as a source
  input; no arithmetic-input constructor from native S.
- SourceCuspDatum and TorsionQuotientBoundaryOrigin are conditional inputs, not
  derived from N8NativeInput.
- The boundary SourceCuspClause requires a Real epsilon/cuspScale card; the
  native record has no such field and no map from its q/Tate data to that card.

Missing source theorem/object: D8CuspConstruction at the selected cusp datum,
including the Real epsilon/cuspScale normalization.

### 4. Compatibility

Target: NativeArithmeticCompatibilityTarget / the five arithmetic (Prop, proof)
pairs of SourceDefinition31Data.

Status: EXACT GAP.
- The five slots are explicit source fields: reduction, torsion, orbicurve,
  section, cusp arithmetic compatibility.
- Native S supplies clauses A-F and the arithmetic q/Tate data, but no source
  theorem proving these five compatibility propositions.
- D9CompatibilitySupply records them as supplied pairs; D4D9Supply takes them
  as fields; no production declaration derives them from N8NativeInput.
- The existing Lean O1 gap bundle records the target; it does not fill it.

Missing source theorem/object: D9CompatibilitySupply / the five arithmetic
compatibility source cards.

## O1 Lean file

File: tmp/sheaf/n8/closure/O1SourceCardsActual.lean.

Actual declarations:
- O1SourceCards: exact bundle of the four clause targets.
- O1SourceCardsTarget and component targets.
- o1SourceCardsTarget_iff_components: exact equivalence.
- o1CanonicalSectionLayer: actual D7a canonical place-section layer.
- o1SectionClauseOfLocalGroups: actual conditional SourceSectionClause from
  D7LocalGroupSectionSupply via production d7SectionLayerBridge.
- o1SectionsCardTarget_of_localGroups: conditional section target.
- O1SourceCardsGap: exact missing-data bundle (orbicurve target, D7b supply,
  cusp target, compatibility target).
- O1CardsUnconstructed: not-constructed predicate.

No arbitrary clause, no degenerate orbicurve, no fabricated compatibility proof.

## Consumer / next obligation

O1 target remains open.  The exact order of work is:
1. D6 actual hyperbolic orbicurves X_K, C_K and certified etale fundamental
   groups.
2. D7b local-group section supply for the canonical place-section layer.
3. D8 selected cusp datum plus Real epsilon/cuspScale normalization.
4. D9 five arithmetic compatibility proofs.
Only then can the four cards feed the existing corrected target.

status: statement_compiles = yes (Lean file exits 0); proof_body_checked = local
conditional section only; kernel_closed = no; target_accepted = false.
