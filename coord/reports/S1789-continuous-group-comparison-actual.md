# S1789: R3 (continuous group comparison) for the actual cover category

Date: 2026-11-01

Lean: `tmp/sheaf/xif/paper/S1789ContinuousGroupComparisonActual.lean`

EXIT=0 (plain `lake env lean` check and `lake env lean -o` olean build)

SHA256 (source): FF4C173CE32D26AF49114E4A5CC6DE401B696D5809E723B6C739661CCF862A28
Source size: 21389 bytes.

olean: `D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1789ContinuousGroupComparisonActual.olean`
(491568 bytes).  A byte-identical copy is next to the source at
`tmp/sheaf/xif/paper/S1789ContinuousGroupComparisonActual.olean`.

SHA256 (olean): 154F038A75888B4CAE5C885CC4080A9C2CF4E781CC0E1C6514CAE32D85659A85

Logs: `tmp/sheaf/xif/paper/logs/S1789_final_check.log` (plain check, EXIT=0) and
`tmp/sheaf/xif/paper/logs/S1789_final_olean.log` (olean build, EXIT=0, axiom audit).

No `sorry`, `admit`, new axiom, `Shrink`, `ULift`, `PLift`, `PUnit` in the code.  The
only literal occurrences of those tokens are in the module doc header.  No fake category, group,
action or fibre functor; no inhabitant of R3, of the certificate, of the small model or of the
datum is fabricated.

## Verdict

**R3 = S1754S1726ComparisonMissing is MISSING.**  No continuous group isomorphism
`(AbsoluteGaloisProfinite F' : Type) ≃ₜ* Aut fiber` is constructed, because none of the
prerequisites exists in the tree.  What the file does is prove exactly what R3 is equivalent to
and record the missing inputs as types, so that nothing weaker (a bare `≃*`, an action, a group
isomorphism for a different category) can stand in for it.

## What is proved (all kernel-checked, axioms only `propext`, `Classical.choice`, `Quot.sound`)

1. `S1789Certificate`: the arithmetic certificate for a general Galois category `C`, fibre
   functor `Fib` and compact topological group `G` - an action on every fibre plus
   `PreGaloisCategory.IsFundamentalGroup Fib G` for that action.
   * `S1789Certificate.comparison` : certificate -> `G ≃ₜ* Aut Fib` (Mathlib `toAutHomeo`
     with `toAutMulEquiv`).  This is the datum-wrapped `S1740ToAutContinuous` of S1740, for a
     bare certificate.
   * `S1789Certificate.ofComparison` : R3 -> certificate, action = transported tautological
     `Aut Fib` action, certificate = `S1741.isFundamentalGroup_of_continuousMulEquiv`.
   * `S1789Certificate.nonempty_iff` : `Nonempty (certificate) ↔ Nonempty (G ≃ₜ* Aut Fib)`.

2. For the actual S1726 cover type
   (`[Category.{0} S1754S1726Cover] [GaloisCategory ...] (fiber) [FiberFunctor fiber]`):
   * `S1789ActualComparison fiber = S1789Comparison fiber (AbsoluteGaloisProfinite F')` is an
     `abbrev` of R3;
   * `S1789ActualComparison_eq_S1754` : it is **definitionally** S1754's
     `S1754S1726ComparisonMissing` at `G = AbsoluteGaloisProfinite F'` (`rfl`);
   * `S1789ActualComparison_iff_certificate` : R3 (for the actual cover type) ↔ the arithmetic
     certificate `S1789ActualCertificate fiber`.

3. `S1789ActualPieces`: S1754's `S1754Pieces` with `action` and `isFundamentalGroup`
   replaced by the single comparison R3 (the other nine fields unchanged).
   * `S1789ActualPieces.toPieces` : pieces -> `S1754Pieces S1726K S1726Orbicurve
     (AbsoluteGaloisProfinite F')` (action from R3, certificate from S1741);
   * `S1789ActualPieces.toDatum` : pieces -> `Iut.OrbicurveEtaleFundamentalGroup
     S1726Orbicurve (AbsoluteGaloisProfinite F')`;
   * `S1789ActualPieces.ofPieces` : `S1754Pieces` -> pieces (the two group fields combine into
     R3);
   * `S1789ActualPieces.nonempty_iff_pieces` : `Nonempty pieces ↔ Nonempty S1754Pieces`;
   * `S1789ActualPieces.nonempty_iff_datum` : `Nonempty pieces ↔
     Nonempty (OrbicurveEtaleFundamentalGroup S1726Orbicurve (AbsoluteGaloisProfinite F'))`,
     using S1754's `S1754Pieces.nonempty_iff`.

4. The small model / Category prerequisite is recorded and tied to S1728:
   * `S1789SmallModelMissing : Type 1 := { coverCategory : Category.{0} S1754S1726Cover //
     S1754S1726StrictRealizationMissing coverCategory }` (S1754 R1, S1728 smallness);
   * `S1789SmallModelMissing.smallRawCoverData` : it implies S1728's exact
     `S1728SmallRawCoverDataRequired`, i.e. a `Type 0` carrier per hom equivalent to the actual
     cover maps.  So P1 is literally S1728's requirement, not a new one;
   * `S1789FiberIdentificationMissing` : S1754 R2 for a chosen small category and fibre functor;
   * `S1789CertificateMissing` : the arithmetic certificate (= R3 by 2).

5. S1748: `s1789FiniteEtaleFiberComparison` is S1748's
   `autFiberEquivOfSurjective` :
   `PostcompSurjective -> (Aut (fiber K Kbar) ≃* (Kbar ≃ₐ[K] Kbar))`,
   reused unchanged.  `S1789PostcompMissing` names the hypothesis.
   `S1789AbsoluteGaloisProfinite_eq` : `(AbsoluteGaloisProfinite K : Type) =
   (SeparableClosure K ≃ₐ[K] SeparableClosure K)` (`rfl`).
   `S1789FieldModelTransfer` records the exact transfer datum (small category + equivalence with
   `(CommAlgCat.FiniteEtale K)ᵒᵖ` + the `≃ₜ*` group comparison) that would turn S1748 into R3;
   no field of it exists in the tree.

6. S1740 / `ContAction`: `S1789AllActionsContinuousMissing` is S1740's
   `S1740AllActionsContinuous (AbsoluteGaloisProfinite F')` for the literal group, its upgrade
   condition.  S1740's correspondence is conditional on the actual datum (hence on R3 and on 3),
   so the `ContAction` model does not supply R3 either.

## Exact prerequisite chain for R3 (recorded as types)

1. P1: `S1789SmallModelMissing` - a `Category.{0}` on the actual cover type with hom-wise
   equivalence to the actual cover maps (S1728 / S1754 R1).  The actual cover-map type is
   `Type 1`, so a small carrier is necessary (S1728).
2. P1b: `GaloisCategory` for that small category (does not follow from P1; Mathlib has no
   `PreGaloisCategory` instance for finite etale algebras either, S1748 section 10).
3. P2: a fibre functor `fiber : S1754S1726Cover ⥤ FintypeCat.{0}` with
   `PreGaloisCategory.FiberFunctor fiber` and the geometric-fibre identification
   `S1789FiberIdentificationMissing` (S1754 R2).
4. P3: R3 itself, equivalently `Nonempty (S1789ActualCertificate fiber)`, i.e. an action of
   `AbsoluteGaloisProfinite F'` on every fibre with
   `PreGaloisCategory.IsFundamentalGroup fiber (AbsoluteGaloisProfinite F')`.

R3 together with P1, P1b, P2 is equivalent to the full S1726 datum (item 3); R3 alone is not
derivable from S1748 (item 5) or from S1740/`ContAction` (item 6).

## Axiom audit

`#print axioms` for `S1789Certificate.comparison`, `ofComparison`, `nonempty_iff`,
`S1789SmallModelMissing.smallRawCoverData`, `S1789ActualComparison_eq_S1754`,
`S1789ActualComparison_iff_certificate`, `S1789ActualPieces.toPieces`, `toDatum`,
`nonempty_iff_pieces`, `nonempty_iff_datum`, `s1789FiniteEtaleFiberComparison`,
`S1789AbsoluteGaloisProfinite_eq`: each depends only on `propext`, `Classical.choice` and
`Quot.sound`.  No `sorryAx`.

## Next executable step

Supply P1 (S1728's `S1728SmallGaloisModel` or the small raw cover data), P1b (Galois category
for the small model), P2 (fibre functor + geometric identification); then R3 is exactly the
remaining arithmetic certificate and can be attacked through S1748's field comparison only after
constructing `S1789FieldModelTransfer`.
