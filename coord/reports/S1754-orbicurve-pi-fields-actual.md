# S1754: actual field values and exact residuals for OrbicurveEtaleFundamentalGroup

Date: 2026-11-01

Lean: tmp/sheaf/xif/paper/S1754OrbicurvePiFieldsActual.lean

EXIT=0 (both `lake env lean` check and `lake env lean -o ...` olean build)

SHA256 (source): AE6C07889994B7B9D5C86D197FDBC57AF75A7C09E5182CE09729EBC1B6674E33

Source size: 28446 bytes.

olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1754OrbicurvePiFieldsActual.olean (888400 bytes)

SHA256 (olean): D0305ADBBB61B60BAC3F5A2CA27620C517A52AC9DA5F714FC9781DE69735CD90

(The same olean was copied next to the source: tmp/sheaf/xif/paper/S1754OrbicurvePiFieldsActual.olean.)

No `sorry`, `admit`, new axiom, `Shrink`, `ULift`, `PLift`, `PUnit`, and no fake category, group,
action or fiber functor.  Scan of the source for those tokens only hits the doc header.

## Actual constructions

1. The last two group-theoretic fields are constructed from ONE comparison datum.
   * `s1754ActionOfMonoidHom (e : G →* Aut Fib) (Y : C) : MulAction G (Fib.obj Y)` is
     `MulAction.compHom` of Mathlib's evaluation action of `Aut Fib`; `s1754ActionOfMonoidHom_smul`
     says the action is evaluation (`rfl`).
   * `s1754IsFundamentalGroupOfContinuousMulEquiv (e : G ≃ₜ* Aut Fib)` proves
     `PreGaloisCategory.IsFundamentalGroup Fib G` for that action, by S1741's transport theorem;
     the action identification required there is `rfl` for the transported action.

2. The three object-level categorical fields (coverMorphism, coverMorphism_over,
   coverMorphism_bijective) are EXACTLY a family of bijections of the hom types with the actual
   cover-map structures:

     S1754CoverMapRealization.nonempty_iff :
       Nonempty (S1754CoverMapRealization F X) ↔
         ∀ A B, Nonempty ((A ⟶ B) ≃ Iut.OrbicurveFiniteEtaleCoverMap A B).

   (`ofEquiv`, `toEquiv`, `ofData` give the two directions; the converse direction chooses the
   equivalences with `Classical.choice`.)  Hence no geometric content is hidden in these three
   fields beyond that bijection.

3. The two coherence fields (coverMorphism_id, coverMorphism_comp) extend item 2 to a strict
   hom-wise realization:

     S1754StrictHomEquiv.nonempty_iff :
       Nonempty (S1754StrictCoverMapRealization F X) ↔ Nonempty (S1754StrictHomEquiv F X),

   where `S1754StrictHomEquiv` is a family of equivalences to the actual cover maps compatible
   with identities and composition up to 2-isomorphism.  This is the exact residual for the five
   categorical fields.

4. geometricFiberFintype is NOT an independent field; it is derived from fiberIdentification.
   * `s1754GeometricFiberFintypeOfIdentification` transports `FintypeCat.fintype` along any
     object-level equivalence between the chosen fiber functor and the literal CostructuredArrow
     geometric fiber, producing `Fintype (GeometricFiber baseScheme basePoint cover)`.
   * `s1754GeometricFiberFintypeOfData` reproduces the stored `geometricFiberFintype` field of
     any datum from its `fiberIdentification` field.

5. Every datum supplies both the fiber identification (namely its own fiberIdentification field,
   `s1754FiberIdentificationOfData`, necessity of R2) and the group comparison:
   `s1754ContinuousMulEquivOfData`.  In particular:
   `s1754ContinuousMulEquivOfData (D : OrbicurveEtaleFundamentalGroup X G) :
     (G : Type u) ≃ₜ* Aut D.fiber`, from Mathlib's `toAutHomeo` and `toAutMulEquiv` under D's
   own `IsFundamentalGroup`.  Hence Residual 3 below is exactly equivalent to the two
   group-theoretic fields (necessary and sufficient).

6. Reduced field list and assembly.  `S1754Pieces F X G` has 11 fields: coverCategory,
   galoisCategory, baseScheme, basePoint, fiber, fiberFunctor, real (the five categorical fields),
   fiberIdentification, fiberIdentification_natural, action, isFundamentalGroup.  Then

     S1754Pieces.toDatum : S1754Pieces F X G → OrbicurveEtaleFundamentalGroup X G
     S1754Pieces.ofData  : OrbicurveEtaleFundamentalGroup X G → S1754Pieces F X G
     S1754Pieces.nonempty_iff : Nonempty (S1754Pieces F X G) ↔ Nonempty (OrbicurveEtaleFundamentalGroup X G),

   and `S1754Pieces.smallRawCoverData` shows that every piece list supplies S1728's
   `S1728SmallRawCoverData` with the categorical hom type as the carrier (consistency with the
   S1728 smallness analysis).

7. S1726 instantiation: `S1754S1726Cover`, `S1754S1726Target`, `S1754S1726CoverMap`,
   `S1754S1726BaseScheme` (= S1726AffineOver), `S1754S1726BasePoint` (= identity strong
   transformation), and the three residuals as types (see below), plus
   `S1754S1726ActionAndCertificate` (Residual 3 gives action + certificate).

## Exact residuals for the S1726 datum

R1 (five categorical fields; currently MISSING):
   `S1754S1726StrictRealizationMissing coverCategory`, i.e.
   `Nonempty (S1754StrictHomEquiv)` for the actual cover type — equivalences of the categorical
   hom types with the actual cover maps, compatible with 1 and composition.  S1728 proves that
   any datum implies small raw cover data, so this is a necessary input.  Its first component is
   `Category.{0}` with small hom carriers; the actual cover-map type is Type 1.
   Necessity in the file: `S1754S1726StrictRealizationMissing_of_data`.

R2 (fiber identification; MISSING):
   `S1754S1726FiberIdentificationMissing coverCategory fiber` — an object-level equivalence of
   the chosen fiber functor with the literal geometric fiber at (S1726AffineOver, identity point).
   Its naturality is the remaining coherence field.  Given R2, the finiteness field follows:
   `S1754S1726GeometricFiberFintypeOfIdentification`.

R3 (group comparison; MISSING):
   `S1754S1726ComparisonMissing fiber` = `(G : Type) ≃ₜ* Aut fiber`.  Given R3, both `action`
   and `isFundamentalGroup` follow (`S1754S1726ActionAndCertificate`); conversely every datum
   yields R3 (`s1754ContinuousMulEquivOfData`).

Still missing independently of these residuals: a `Category.{0}` on the actual cover type, a
`GaloisCategory` for it, and a fiber functor to `FintypeCat` (i.e. S1728's first missing + the
Galois/fiber structure).

## Field-by-field status (all 16 fields of OrbicurveEtaleFundamentalGroup at S1726)

| field | status |
| --- | --- |
| coverCategory | MISSING (Category.{0} on a Type 1 type; actual hom Type 1, S1728) |
| galoisCategory | MISSING, depends on coverCategory |
| baseScheme | ACTUAL (S1726AffineOver; S1737, reproduced) |
| basePoint | ACTUAL (identity strong transformation; S1737, reproduced) |
| fiber | MISSING (no functor to FintypeCat in the tree) |
| fiberFunctor | MISSING, depends on fiber |
| coverMorphism | MISSING, exactly R1 |
| coverMorphism_over | MISSING, exactly R1 |
| coverMorphism_bijective | MISSING, exactly R1 |
| coverMorphism_id | MISSING, coherence part of R1 |
| coverMorphism_comp | MISSING, coherence part of R1 |
| geometricFiberFintype | DERIVED from fiberIdentification (item 4); no separate input |
| fiberIdentification | MISSING, exactly R2 |
| fiberIdentification_natural | MISSING, coherence part of R2 |
| action | MISSING, exactly R3 (item 1 + item 5) |
| isFundamentalGroup | MISSING, exactly R3 (item 1 + item 5) |

## Not claimed

No inhabitant of `OrbicurveEtaleFundamentalGroup S1726Orbicurve G`, no Galois category, no
small cover model, no geometric fiber identification and no comparison with the absolute Galois
group are constructed.  The three residuals are recorded as types; nothing is postulated,
shrunk, or replaced by a placeholder.

## Axiom audit

`#print axioms` on all thirteen checked declarations reports only
`propext, Classical.choice, Quot.sound`: S1754CoverMapRealization.nonempty_iff,
S1754StrictHomEquiv.nonempty_iff, s1754GeometricFiberFintypeOfIdentification,
s1754GeometricFiberFintypeOfData, s1754IsFundamentalGroupOfContinuousMulEquiv,
S1754Pieces.toDatum, S1754Pieces.ofData, s1754ContinuousMulEquivOfData,
S1754Pieces.smallRawCoverData, S1754CoverMapRealization.ofData, S1754Pieces.nonempty_iff,
s1754FiberIdentificationOfData, S1754S1726StrictRealizationMissing_of_data.  No `sorryAx`.

## Verification commands

`lake env lean tmp/sheaf/xif/paper/S1754OrbicurvePiFieldsActual.lean` — EXIT=0.

`lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1754OrbicurvePiFieldsActual.olean tmp/sheaf/xif/paper/S1754OrbicurvePiFieldsActual.lean` — EXIT=0.

## Next executable step

Any of R1, R2, R3 can be attacked independently; all three plus the category/fiber structure give
the datum by `S1754Pieces.toDatum`.  Do not spend effort on `geometricFiberFintype`: it follows
from R2.  For the D6 clause the missing group comparison is
`Iut.AbsoluteGaloisProfinite F' ≃ₜ* Aut fiber` (Type 0 vs Type 1 caveat: a small model of
`Aut fiber` may be needed, as in S1741's universe note).
