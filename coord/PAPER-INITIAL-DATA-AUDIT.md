# Paper initial Theta-data audit: SourceInitialThetaData vs SourceDefinition31Data

Date: 2026-10-24
Auditor: transport
Scope: paper source construction only. No wrapper, no arbitrary filler.

## Verdict

SourceInitialThetaData (LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData)
is substantially more paper-faithful than SourceDefinition31Data.
It carries actual place sets, actual orbicurve objects over F/Fmod/K, and
clauses A-F with typed content. SourceDefinition31Data is the later contract
shell audited in PAPER-SOURCE-SEMANTICS-AUDIT.md.

There is NO unconditional record projection
SourceInitialThetaData -> SourceDefinition31Data.  The two contracts are not
record-equivalent; only the arithmetic root is definitionally shared.  This is
the finding already recorded in SourceDefinition31DualContractAlignment.lean.

## What is actually available from SourceInitialThetaData

Actual fields of SourceInitialThetaCandidate:
- arithmetic : InitialThetaArithmeticData l;
- xF, cF : SourceOrbicurveObject arithmetic.F;
- xK, cK : SourceOrbicurveObject arithmetic.K;
- Vmod : Set (NumberFieldPlace Fmod);
- VbadMod : Set (NumberField.FinitePlace Fmod);
- VgoodMod : Set (NumberFieldPlace Fmod), with
  VgoodMod = Vmod \ finite '' VbadMod;
- V : Type, place : V -> NumberFieldPlace K,
  placeToMod : V -> NumberFieldPlace Fmod,
  placeToMod_bijective, placeToMod_mem_Vmod,
  place_comap_compatible;
- epsilonCarrier : Type, epsilon : epsilonCarrier.

Clauses A-F add actual content:
- ClauseA: sqrt(-1), curve signature once-punctured elliptic, stable reduction
  everywhere, maximal solvable extension;
- ClauseB: bad-nonempty, odd residue, stable/multiplicative reduction over bad,
  FinitePlaceQCandidate q with order coprime to l;
- ClauseC: rational 2/3-torsion, canonical Galois representation, SL2
  containment, K-kernel compatibility;
- ClauseD: type (1,l-tors) and (1,l-tors)^+- orbicurve signatures, cartesian
  square, four profinite exact sequences;
- ClauseE: V is a section, Vnon/Varc/Vbad/Vgood definitions, finite/infinite
  local data;
- ClauseF: cusp datum over epsilonCarrier, cusp-derived orbicurves, cusp
  localization, bad/good cusp conditions.

This is the paper object shape: F-bar/F, X_F, l, C_K, V, V^bad_mod, epsilon.

## Why there is no direct projection to SourceDefinition31Data

| paper/legacy field | SourceInitialThetaData carrier | SourceDefinition31Data carrier | mapping status |
|---|---|---|---|
| arithmetic | candidate.arithmetic : InitialThetaArithmeticData | arithmetic : InitialThetaArithmeticData | SHARED; actual projection exists |
| X_F,C_F,X_K,C_K | candidate.xF/cF/xK/cK : SourceOrbicurveObject | orbicurve clause over generic Type/group shell | NO PROJECTION; need actual clauses |
| selected places | Vmod/V : actual sets/type with place maps and bijection | selectedPlaces : bare Type + source partition | PARTIAL mapping possible (V), but bad finiteness/labels not shared |
| bad places | VbadMod : Set (FinitePlace Fmod) | badPlaces : bare Type | actual set is available; need finite subtype, but SourceDefinition31Data does not demand VbadMod/Vmod relation |
| reduction/q | ClauseB stable/multiplicative + FinitePlaceQCandidate q (adic completion) | arbitrary Bad->Prop + Real qParameter | NO MAP adic q -> Real q; split reduction absent |
| torsion | ClauseC actual torsion23 + canonical Galois rep + SL2 containment | abstract torsionCarrier with Fin 6 label + opaque Props | NO MAP; shell is not ClauseC |
| exact sequences/local groups | ClauseD four profinite exact sequences; ClauseE local data | one exact-sequence clause + section shell | NO MAP; need rebuild |
| cusp/epsilon | epsilonCarrier with epsilon + ClauseF cusp | Real epsilon/cuspScale + opaque Prop | NO MAP epsilonCarrier -> Real |
| maximal solvable extension | ClauseA field | none | legacy-only |
| coherence | arithmetic_clause_coherence, clause_order_coherence (opaque) | five arithmetic_*_compatibility Props | NO MAP; both sides opaque, but not the same Props |

Additional mismatches:
- SourceInitialThetaData has actual orbicurve objects, the current contract has
  a generic shell; no field converts SourceOrbicurveObject to
  SourceOrbicurveClause.
- ClauseB q is adic-valued (FinitePlaceQCandidate), the current reduction
  qParameter is Real; no production map.
- ClauseC gives actual torsion/Galois data; the current torsion clause has a
  Fin 6 label and abstract groups; no Fin 6 label extraction is proved.
- ClauseF gives epsilon in epsilonCarrier; the current cusp clause needs Real
  epsilon with positivity; no epsilonCarrier -> Real map.
- There is no maximal solvable extension slot in SourceDefinition31Data.
- The dual contract alignment records that neither direction is constructible
  from present fields.

## PaperInitialThetaData.lean

File: tmp/sheaf/n8/closure/PaperInitialThetaData.lean.
Actual projections:
- paperArithmetic;
- paperVbadMod, paperVmod, paperV, paperPlace, paperPlaceToMod,
  paperPlaceToMod_bijective;
- paperXF, paperCF, paperXK, paperCK;
- paperEpsilonCarrier, paperEpsilon.

Conditional assembly:
- PaperToCurrentDonors bundles exactly the missing clause data:
  reduction over actual V/Vbad subtype, torsion, orbicurve, sections, cusp,
  and the five compatibility slots;
- sourceDefinition31DataOfPaperDonors constructs SourceDefinition31Data with
  arithmetic and V/Vbad carriers from SourceInitialThetaData and all other
  clause fields exactly from donors;
- sourceDefinition31DataOfPaperDonors_arithmetic is rfl;
- PaperToCurrentProjectionGap records that the donor interface is not
  inhabited here.

This is a conditional projection, not an arbitrary filler: the donor fields
are actual source clause objects, and the file does not construct them.

## OriginalInput mapping gap

OriginalInput requires SourceDefinition31Data plus a SourceHodgeTheaterFamily,
an index equivalence family.index ≃ Int × Int, and arithmetic alignment.
SourceInitialThetaData does not contain a Hodge-theater family or its index
equivalence.  Even if the conditional SourceDefinition31Data above is supplied,
OriginalInput remains a separate construction:
- need a SourceHodgeTheaterFamily (prime-strip family + link system);
- need index equivalence to Int × Int;
- need alignment of each theater arithmetic with the initial arithmetic.
No such family is constructed from SourceInitialThetaData clauses here.
Exact gap: MissingHodgeTheaterFamilyFromPaperSource.

## C6 tensor places/tuple/measure note for primespine

The actual C6 tensor carrier API is in
LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceArithmeticTensorBlocks.lean:
ArithmeticTensorTupleBlock places tuple, where
places : (i : ι) -> V i -> FinitePlaceAtPrime K p, tuple : (i : ι) -> V i,
with Fintype ι and a measure/IsAddHaarMeasure input for the canonical hull.

SourceInitialThetaData supplies:
- actual K and Fmod, actual V/place/placeToMod with bijection;
- ClauseB actual finite places over bad moduli, q candidates;
- ClauseD orbicurve objects (not tensor index/places).

It does NOT directly supply:
- a chosen rational prime p and the map V -> FinitePlaceAtPrime K p
  (place : V -> NumberFieldPlace K is not typed at a prime);
- the finite tensor index ι and tuple (i) -> V i;
- the measure / IsAddHaarMeasure on ArithmeticTensorTupleBlock.
These are exact missing inputs for a C6PaperDivisor construction.  No C6 tensor
places/tuple/measure is constructed from SourceInitialThetaData in this file.

## Recommended source route

Use SourceInitialThetaData, not SourceDefinition31Data, as the paper source
candidate.  For downstream C9/C7:
1. Keep actual candidate arithmetic and actual place/orbicurve data.
2. Build the current SourceDefinition31Data only through the exact donor
   interface, never by degenerate filling.
3. Build a Hodge-theater family and OriginalInput from an actual source family,
   not from the shell.
4. For C6, first construct the chosen prime p, the finite place-indexed family
   at p, the tuple and the Haar measure; those are not SourceInitialThetaData
   projections.

## Constructed paper-to-current donors

File: tmp/sheaf/n8/closure/PaperToCurrentDonorsConstructed.lean.

Actual construction from SourceInitialThetaData clauses A/B:
- PaperBadPlaces = {p : FinitePlace Fmod // p in candidate.VbadMod};
- paperPlaceEquiv : candidate.V ≃ NumberFieldPlace Fmod from
  candidate.placeToMod_bijective;
- paperBadLift : bad Fmod-place -> finite F-place via comap_surjective;
- paperBadStable from clauseA.stable_reduction_everywhere;
- paperBadMultiplicative from clauseB.multiplicative_over_bad;
- paperQCandidate and paperQParameter = exp(-order) from clauseB.qParameter;
- q nonzero/contracting/q != 1 proved.
- paperReductionClause assembles SourceReductionClause from these actual
  fields plus donors badFinite/labels/split-multiplicative.

Exact remaining donors:
- PaperReductionDonors: badFinite, selectedLabel, badLabel,
  label_compatible, splitMultiplicativeReduction;
- PaperRemainingClauseDonors: torsion, orbicurve, sections, cusp and the five
  compatibility pairs.
- paperToCurrentDonors combines them with the actual reduction clause;
- paperSourceDefinition31Data = PaperInitialThetaData.sourceDefinition31DataOfPaperDonors.

Why torsion/orbicurve/sections/cusp are not directly constructed:
- SourceTorsionClause needs a Fin 6 labelled group carrier; ClauseC supplies
  actual torsion23/Galois representation but no Fin 6 label/group carrier.
- SourceOrbicurveClause needs curve/punctured/cover carriers and a full exact
  sequence clause; ClauseD supplies signatures and morphisms but not those
  generic clause fields.
- SourceSectionClause needs local-group carriers and pointwise bijections;
  ClauseE supplies local data at finite/infinite indices, not a direct
  pointwise section structure.
- SourceCuspClause needs Real epsilon/cuspScale; ClauseF supplies a cusp datum
  over epsilonCarrier, with no epsilonCarrier -> Real map.

These are precise donor fields, not arbitrary fill.

status: statement audit plus constructed donor file; target_accepted=false.
