# S1809: actual small-carrier Category.{0,1} on the S1726 cover type

Date: 2026-11-01

Lean: tmp/sheaf/xif/paper/S1809SmallCarrierCategoryActual.lean

EXIT=0

SHA256 (source): 5CAED79EFDF1341EA26601732D2F28D2C2BB34EBC2E1A34CC1392B64BEBC0BC5

olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1809SmallCarrierCategoryActual.olean
(77592 bytes, SHA256
6881389C2A1BBA8E5A92CD0C902C5B48391DF5A34D38AFAD8EC7121ED1B8023B)

## Question

S1728 constructed the genuine Category.{1,1} on the actual S1726 cover type
(S1728ActualCategory11, homs = 2-isomorphism classes of cover maps) and named
the target field

  S1728CoverCategoryFirstMissing = Category.{0,1} S1728Cover

as missing, together with S1728SmallRawCoverDataRequired.  S1766 then
constructed the unconditional Type-0 small model

  S1766QuotSmallCarrier A B = Set.range (S1766QuotAct A B) : Type
  S1766QuotSmallEquiv A B : Quot (S1728CoverMapRel A B) ≃ S1766QuotSmallCarrier A B

(the canonical action is injective on the 2-isomorphism quotient, unconditionally).
Task: transport the S1728 Category.{1,1} along this carrier/equivalence to the
actual cover category at Category.{0,1}, construct Category.{0,1} S1728Cover and
S1728SmallRawCoverDataRequired, and if raw CoverMapDiscrete or an extra
equivalence is needed, state the exact first missing.

## Actual constructions (unconditional)

* S1809CoverCategory01 : Category.{0,1} S1728Cover.  It is
  S1728CategoryOfHomEquiv S1728ActualCategory11 with
  H := S1766QuotSmallCarrier and e := (S1766QuotSmallEquiv).symm.
  Its hom family is literally S1766QuotSmallCarrier (a Type 0 type), and its
  identity/composition are the transported actual quotient operations
  (S1809CoverCategory01_hom : the hom type is the carrier, by rfl).
  No discreteness, no Shrink/ULift/PLift/PUnit, no redefinition of objects.

* S1809CoverCategoryFirstMissing_inhabited : S1728CoverCategoryFirstMissing
  and S1809TargetCoverCategory_inhabited : S1728TargetCoverCategory.  The first
  missing categorical field of S1728's target is therefore discharged
  unconditionally.

* S1809ComparisonFunctor : S1809CoverCategory01 ⥤ S1728ActualCategory11,
  identity on objects and S1766QuotSmallEquiv on homs.  It is Full, Faithful
  and EssSurj (instances), hence S1809ComparisonFunctor_isEquivalence :
  S1809ComparisonFunctor.IsEquivalence.  Thus the small category is the actual
  2-isomorphism quotient category of cover maps at the target hom universe, not
  a different or degenerate category.

## Raw small cover data: exact first missing (conditional part)

* The raw cover-map type is genuinely Type 1: S1728CoverMap A B : Type 1, and
  it does not fit Type 0 (checked: Carrier := S1728CoverMap A B is rejected by
  the universe checker).  Hence a small carrier with an equivalence is
  necessary for S1728SmallRawCoverData.

* The canonical construction of the raw small datum from the small carrier has
  exactly one missing input:

    S1809SmallRawCoverDataFirstMissing := S1766CoverMapDiscrete

  (S1766's residual R2a: every 2-isomorphism class of cover maps is a
  singleton).  The file proves the exact characterizations

  - S1809SmallRawCoverDataFirstMissing_iff_S1766 :
      ↔ S1766RawInjectivityExactMissing
  - S1809SmallRawCoverDataFirstMissing_iff_quotMk_injective :
      ↔ injectivity of Quot.mk on every pair of actual covers
  - S1809SmallRawCoverDataFirstMissing_iff_section :
      ↔ a retraction of Quot.mk (one chosen representative per class)
  - S1809SmallRawCoverDataFirstMissing_iff_rawInjective :
      ↔ S1744CanonicalModelHomActionInjective
        S1744CanonicalModelHomActionActual

  and, from it,

  - S1809QuotEquivRaw : Quot (S1728CoverMapRel A B) ≃ S1728CoverMap A B
  - S1809SmallRawCoverDataOfFirstMissing :
      S1728ActualSmallRawCoverData A B with
      Carrier := S1766QuotSmallCarrier A B
  - S1809SmallRawCoverDataRequired_of_firstMissing :
      S1809SmallRawCoverDataFirstMissing → S1728SmallRawCoverDataRequired.

* No inhabitant of S1728SmallRawCoverDataRequired is asserted, and the reverse
  implication (raw smallness → discreteness) is neither asserted nor used: the
  quotient carrier only determines the 2-isomorphism quotient, not the raw
  class map.  The first missing on this route is exactly the S1766 residual
  above, not a new geometric assumption.

* The only remaining categorical field of OrbicurveEtaleFundamentalGroup on
  top of the new category is recorded as

    S1809GaloisCategoryRequired := @GaloisCategory.{1,0} S1728Cover
      S1809CoverCategory01

  with no inhabitant.

## Honest boundary

No sorry, no new axiom, no Shrink/ULift/PLift/PUnit, no fake category.  The
Category.{0,1} and its equivalence to the quotient category are unconditional;
the raw smallness statement is conditional on the named S1766 residual
S1766CoverMapDiscrete.  No GaloisCategory is constructed.

## Evidence

- Lean: tmp/sheaf/xif/paper/S1809SmallCarrierCategoryActual.lean
  (327 lines, 13650 bytes, SHA256
  5CAED79EFDF1341EA26601732D2F28D2C2BB34EBC2E1A34CC1392B64BEBC0BC5).
- Build: lake env lean -o
  .lake/build/lib/lean/tmp/sheaf/xif/paper/S1809SmallCarrierCategoryActual.olean
  tmp/sheaf/xif/paper/S1809SmallCarrierCategoryActual.lean
  EXIT=0, no warnings, no sorryAx.
- Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1809SmallCarrierCategoryActual.olean
  (77592 bytes, SHA256
  6881389C2A1BBA8E5A92CD0C902C5B48391DF5A34D38AFAD8EC7121ED1B8023B).
- Consumer check (separate scratch file, since deleted): importing
  tmp.sheaf.xif.paper.S1809SmallCarrierCategoryActual and using
  S1809CoverCategory01 : Category.{0,1} S1728Cover,
  S1809CoverCategoryFirstMissing_inhabited,
  S1809SmallHom : ... → Type, and
  S1809SmallRawCoverDataRequired_of_firstMissing compiled with EXIT=0.
- Axiom audit: every #print axioms reports only propext, Classical.choice and
  Quot.sound; S1809EqvGen_to_rel depends on no axioms.

Environment note: during this session the transitive project oleans
LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31RootLemmas.olean and
SourceDefinition31Quantifiers.olean (imports of S1726OrbicurveFPrimeActual,
hence of S1766) were temporarily absent while other agents rebuilt them.  The
final compile was run after both were restored; the S1809 source is unaffected.

## Statement / closure status

- statement_compiles = yes (Category.{0,1} S1728Cover with explicit hom carrier,
  the target field types, and the raw first-missing statements).
- proof_body_checked = yes for all declarations listed above.
- kernel_closed = yes (axiom trio only, no sorryAx).
- target_accepted = false: the OrbicurveEtaleFundamentalGroup is not
  constructed; the Galois field S1809GaloisCategoryRequired, the fiber functor,
  coverMorphism, action and the remaining target fields are untouched; the raw
  small cover data remains conditional on S1766CoverMapDiscrete.

## Consumer

Directly: S1728's S1728CoverCategoryFirstMissing / S1728TargetCoverCategory
(first missing target field now inhabited), and any later assembly of
OrbicurveEtaleFundamentalGroup S1726Orbicurve G at G = ProfiniteGrp.{0}, which
now only needs the Galois field and the remaining structural fields, not the
cover category.  The same construction transports any future GaloisCategory
proved on the small side, via S1809ComparisonFunctor (an equivalence).

## Next executable step

Either (a) prove S1766CoverMapDiscrete (equivalently raw R2a) to discharge
S1728SmallRawCoverDataRequired, or (b) attack the Galois field
S1809GaloisCategoryRequired on S1809CoverCategory01 (and the fiber functor /
coverMorphism / action fields), which no longer depends on the cover-category
smallness problem.  A counterexample with a nontrivial 2-isomorphism class of
cover maps would refute (a) via S1766_collision and would make the raw
requirement genuinely unprovable, while leaving S1809CoverCategory01 intact.
