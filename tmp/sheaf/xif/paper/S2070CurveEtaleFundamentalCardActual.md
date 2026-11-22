# S2070 — CurveEtaleFundamentalGroupCard: actual construction or exact first missing

Task: construct an inhabitant of
`LeanFormal.IUT.IUTII.Frobenioid.Example36.CurveEtaleFundamentalGroupCard K`
for the once-punctured curve y^2 = x^3 - x (E \ {O}), or give the exact first
missing. No fake, no `Nonempty` gate, no substituted category.

Deliverable: `tmp/sheaf/xif/paper/S2070CurveEtaleFundamentalCardActual.lean`.

## Evidence

| item | value |
|---|---|
| Lean | `lake env lean -o ...` , **EXIT = 0** |
| wall time | 83 s (plain run, no `-o`); ~3 s extra with `-o` |
| source SHA-256 | `3942B353871D9779E9A47417F39C5C80035C9D9EBC709471B35ECB62C00D110F` |
| source size | 27579 bytes, 542 lines |
| olean | `tmp/sheaf/xif/paper/S2070CurveEtaleFundamentalCardActual.olean`, 295176 bytes |
| olean SHA-256 | `704549CD7BAC64C860105C33AC1F92E29A97C7EE35DB76983FE324303A04C191` |
| sorries / axioms in source | none (grep for sorry|admit|^axiom is empty) |
| build prerequisite | rebuilt `LeanFormal.IUT.IUTII.Frobenioid.Example36CurveGaloisCategory` (its olean had been removed by an interrupted `lake build`); `lake build ...Example36CurveGaloisCategory` -> Build completed successfully (4288 jobs) |

Axioms (`#print axioms`, all seven audited declarations):
`[propext, Classical.choice, Quot.sound]` — nothing else.
Audited: `preGaloisCategory_of_hasQuotients`, `preGaloisCategory_of_remainingFields`,
`curveEtaleCover_monoInducesIsoOnDirectSummand`, `fiberFunctor_of_certificate`,
`profiniteAut_isFundamentalGroup`, `curveEtaleFundamentalGroupCardV_realized_of_certificates`,
`galoisCategory_curve_of_certificates`.

## Answers to the four task items

### (1) coverCategory / fiber — DONE, with the actual objects

* `CurveEtaleCoverCategory K := FiniteEtaleCover (puncturedEllipticCurveScheme K)`
  from `IUT/Foundations/Geometry/CurveEtaleFundamentalGroup.lean`, i.e.
  `ObjectProperty.FullSubcategory (Etale ∧ IsFinite over X)`, with
  `Category.{u, u+1}`.  It is `rfl`-equal to the `Example36` cover category
  (`curveEtaleCoverCategory_eq`), and `puncturedEllipticCurveScheme K` is
  `rfl`-equal to `Example36.curveScheme K` (`curveBase_eq_curveScheme`).
* `fiber := curveGeometricFiberFunctor K Omega x := geometricFiberFunctor Omega x`,
  the actual geometric fiber functor `Y ↦ { s : Spec Omega → Y // s ≫ f = x }`.
* The `FintypeCat`-valued version `curveGeometricFiberFunctorFintype K hfin` is
  constructed as `ObjectProperty.lift (fun T => Finite T) ...`, together with the
  `rfl` lemma `..._comp_incl : (lift) ⋙ FintypeCat.incl = curveGeometricFiberFunctor`,
  so the lift is provably not a substitution.  It is conditional on
  `GeometricFiberFinite` (below), which is genuinely missing.

### (2) PreGaloisCategory / GaloisCategory / IsFundamentalGroup

* `PreGaloisCategory (FiniteEtaleCover X)` is reduced to **exactly one** missing
  field.  Four of the five fields are already theorems in the tree and are
  restated here (rfl): terminal (G1) `curveEtaleCover_hasTerminal`, pullbacks (G1)
  `curveEtaleCover_hasPullbacks`, finite coproducts (G2)
  `curveEtaleCover_hasFiniteCoproducts`, direct summands (G3)
  `curveEtaleCover_monoInducesIsoOnDirectSummand`.
* `preGaloisCategory_e36` assembles `PreGaloisCategory` from the four theorems
  plus the single missing field; `preGaloisCategory_of_hasQuotients` transports it
  to the actual cover category; `preGaloisCategory_of_remainingFields` consumes
  the **existing frozen tree card**
  `CurvePreGaloisCategoryRemainingFields` (Example36CurveGaloisCategory.lean:330);
  `preGaloisCategory_of_affineBaseG2` reduces further to the affine base
  `Spec K[x,y]/(y^2-x^3+x)` (the `SourceCurveG2Quotients` reduction, restated).
* `IsFundamentalGroup` — **fully proved**, not missing.
  `aut_isFundamentalGroup` and `profiniteAut_isFundamentalGroup` are
  `inferInstance` from Mathlib's `PreGaloisCategory.IsFundamentalGroup F (Aut F)`
  (Mathlib/CategoryTheory/Galois/IsFundamentalgroup.lean:251).
* `GaloisCategory` — reduced to `PreGaloisCategory` + one fiber functor
  (`galoisCategory_of_fiberFunctor`, `galoisCategory_curve_of_certificates`).

### (3) ProfiniteGrp structure — DONE, and no profinite completion is needed

`Aut F` **is already profinite in Mathlib**: Mathlib/CategoryTheory/Galois/Topology.lean
gives `CompactSpace (Aut F)`, `T2Space`, `TotallyDisconnectedSpace`,
`IsTopologicalGroup` for any `F : C ⥤ FintypeCat` (no Galois hypotheses).
Hence `fiberAutProfiniteGrp F := ProfiniteGrp.of (Aut F) : ProfiniteGrp.{u+1}`,
and `profiniteAut_isFundamentalGroup : IsFundamentalGroup F (ProfiniteGrp.of (Aut F))`.
**Answer to the task's open question: neither a profinite completion of `Aut F`
nor an abstract fundamental-group input is required.**  The only universe care
needed is that `Aut F` sits in `Type (u+1)` for `C : Type (u+1)`,
`Category.{u,u+1}`, `F : C ⥤ FintypeCat.{u}`.

### (4) Exact first missing

**First missing (obstruction), independent of all mathematics: the frozen card has
a one-universe offset and cannot be instantiated with the actual covers.**

`CurveEtaleFundamentalGroupCard.{u} (K : Type u)` demands

* `coverCategory : Type u` and `Category.{u, u}`,
* `fundamentalGroup : ProfiniteGrp.{u}` (carrier in `Type u`),

whereas for `K : Type u`

* `FiniteEtaleCover (puncturedEllipticCurveScheme K) : Type (u+1)` with
  `Category.{u, u+1}` (checked: `#check @FiniteEtaleCover` gives
  `Scheme.{u_1} → Type (u_1+1)`; the instance is `Category.{u, u+1}`),
* the fiber-functor automorphism group lives in `Type (u+1)`
  (`#check curveEtaleFundamentalGroup` gives `... → Type (u_1+1)`;
  `#check (CategoryTheory.Aut F)` with `F : C ⥤ FintypeCat.{u}`,
  `C : Type (u+1)` gives `Aut F : Type (u+1)`, hence `ProfiniteGrp.{u+1}`).

All three are uniformly one universe too small.  Raising `K` by `ULift` does not
help: the cover category is always exactly one universe above `K`.  The
corrected card is `CurveEtaleFundamentalGroupCardV` (every universe +1), which is
the same structure with the same nine fields.

**First missing (mathematical), after the universe correction.**  The corrected
card has exactly two mathematical obligations; its `geometricPiOne : ProfiniteGrp`
and `geometricConnectedness : Prop` fields have **no property attached at all**
and its `fundamentalGroup` / `action` / `isFundamentalGroup` fields are produced
by Mathlib from any fiber functor.  This is proved by `mkCardV`, which is fully
generic in `C` and `F`:

* **(M1)** `CurveQuotientsByFiniteGroups K` : quotients of finite étale covers by
  finite group actions, i.e. `∀ (G : Type u) [Group G] [Finite G],
  HasColimitsOfShape (SingleObj G) (FiniteEtaleCover X)`.  The single missing
  `PreGaloisCategory` field.  Not in Mathlib in any form: the only
  `HasColimitsOfShape (SingleObj G)` instances are for `FintypeCat` and
  `Action FintypeCat G` (Galois/Examples.lean:76,86); there is no scheme
  quotient by a finite group in Mathlib 4.32.2, and nothing in the tree.
  Required: (a) a categorical quotient `Y//G` of a scheme by a finite group with
  `Y → Y//G` finite étale, (b) that it is the colimit of the `SingleObj G`
  diagram in `FiniteEtaleCover X`, (c) base-change compatibility.
* **(M2)** `GeometricFiberFinite K Omega x` : for a field `Omega`, a geometric
  point `x : Spec Omega → X` and a finite étale cover `Y → X`, the type of lifts
  `{ s : Spec Omega → Y // s ≫ (Y → X) = x }` is finite.  True (finite morphisms
  have finite fibers) but absent.  Required: (a) Mathlib *has* `IsFinite` stable
  under base change; (b) *missing*: a scheme finite over `Spec Omega` is affine
  with a finite `Omega`-module ring, and lifts are `Omega`-algebra maps out of it;
  (c) *missing*: a finite-dimensional algebra over a field has finitely many
  maximal ideals, so finitely many `Omega`-algebra maps to `Omega`.
* **(M3)** `FiberFunctorCertificate (curveGeometricFiberFunctorFintype K hfin)` :
  the six (G4)-(G6) obligations, frozen verbatim as a `Prop` structure
  (`preservesTerminalObjects`, `preservesPullbacks`, `preservesFiniteCoproducts`,
  `preservesEpis`, `preservesQuotientsByFiniteGroups`, `reflectsIsos`).
  `fiberFunctor_of_certificate` is the exact conversion.

So (M1)+(M2)+(M3) imply `GaloisCategory (FiniteEtaleCover X)`, which implies the
corrected card (`curveEtaleFundamentalGroupCardV_realized_of_certificates`).

**Not fabricated.**  `geometricPiOne` (the geometric kernel of
`pi_1^et(X) → G_K`) is *not* guessed: the comparison morphism
`pi_1^et(X) → pi_1^et(Spec K)` does not exist in the tree, and the card does not
require it, so the corrected card takes it as a caller-supplied parameter with a
docstring saying so.  For `geometricConnectedness` we do supply genuine content:
`curveGeometricConnectedness K := ConnectedSpace (CurveBase K)`, proved
(`curveGeometricConnectedness_holds`, from `curveOncePunctured_connected`).

## Audit note on the frozen card

The frozen `CurveEtaleFundamentalGroupCard` is *structurally too weak* to express
the étale fundamental group of the curve: `coverCategory` is an unconstrained
`Type u` (nothing ties it to `FiniteEtaleCover X`), `geometricPiOne` is an
unconstrained `ProfiniteGrp`, and `geometricConnectedness` is an unconstrained
`Prop`.  `mkCardV` inhabits the corrected card from *any* Galois category with
*any* fiber functor.  Consequently realising the card "for the curve" is exactly
the Galois-category certificate, and any future use of the card should (a) be
universe-corrected and (b) gain a field tying `coverCategory` to the actual
covers (e.g. an iso to `FiniteEtaleCover X`); otherwise the card can be discharged
without any curve content.

## Next executable step (one)

Prove (M1) for the affine base `Spec K[x,y]/(y^2-x^3+x)` — the scheme-level
quotient-by-finite-group theorem for a finite étale cover of an affine base — then
feed it through `preGaloisCategory_of_affineBaseG2`.  This unlocks
`PreGaloisCategory`, hence `MonoCoprod`, `HasFiniteLimits` and the Mathlib Galois
API for the curve.  (M2)/(M3) are independent and can proceed in parallel.

## Files touched

* added: `tmp/sheaf/xif/paper/S2070CurveEtaleFundamentalCardActual.lean` (this package)
* added: `tmp/sheaf/xif/paper/S2070CurveEtaleFundamentalCardActual.olean`
* added: `tmp/sheaf/xif/paper/S2070CurveEtaleFundamentalCardActual.md` (this report)
* rebuilt (not modified): `LeanFormal/IUT/IUTII/Frobenioid/Example36CurveGaloisCategory.olean`
  (and its upstream oleans) — restored after an interrupted `lake build`;
  sources unchanged.
