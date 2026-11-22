# S2088 -- FiberFunctorCertificate for curveGeometricFiberFunctorFintype: item-by-item proof / exact first missing

Task: for `curveGeometricFiberFunctorFintype K hfin` (S2070/S2074, with the
finiteness input discharged by S2081), settle the six fields of the S2070
`FiberFunctorCertificate`: preservesTerminalObjects, preservesPullbacks,
preservesFiniteCoproducts, preservesEpis, preservesQuotientsByFiniteGroups, reflectsIsos.

Deliverable: `tmp/sheaf/xif/paper/S2088FiberFunctorCertificateActual.lean`
(380 lines, 21938 bytes).

## 1. Build evidence

| item | value |
|---|---|
| compile command | `lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2088FiberFunctorCertificateActual.olean tmp/sheaf/xif/paper/S2088FiberFunctorCertificateActual.lean` |
| EXIT | **0** |
| olean | `.lake/build/lib/lean/tmp/sheaf/xif/paper/S2088FiberFunctorCertificateActual.olean`, 168040 bytes |
| SHA256 (lean) | `E70B128588CF63645CE7E4436A4C19B383DCBCEB82170F023DBA84F151097CFE` |
| SHA256 (olean) | `777A4B19EC0ED1720EEC6E74BCAECE558FD9101E4B8704963E97AD9724744DF7` |
| target-lock | `tmp/sheaf/xif/paper/_S2088TargetLock.lean` compiles, EXIT=0: the field types of `FiberFunctorCertificate` are matched against the theorems, and the unconditional inhabitant of field 1 is checked |
| axioms | every audited theorem depends only on `propext, Classical.choice, Quot.sound`; no `sorryAx`, no custom axiom |

## 2. Item-by-item result

1. **preservesTerminalObjects -- PROVED unconditionally.**
   `certificate_preservesTerminalObjects (hfin)`, of type
   `PreservesLimitsOfShape (Discrete PEmpty.{1}) (curveGeometricFiberFunctorFintype K hfin)`.
   Proof chain: `isTerminal_obj_of_isTerminal` (a terminal cover is
   isomorphic to the identity cover, whose fiber is the singleton of the
   geometric point) -> `preservesLimit_empty` (via
   `isLimitMapConeEmptyConeEquiv` and
   `finiteEtaleCover_terminalCover_isTerminal`) ->
   `preservesLimitsOfShape_pempty_of_preservesTerminal` ->
   transfer to the FintypeCat-valued lift.  No `Etale`/finiteness input beyond hfin.

2. **preservesPullbacks -- ISOLATED (exact statement; formalization gap of this file only).**
   Theorems: `certificate_preservesPullbacks` takes the hypothesis
   `PreservesLimitsOfShape WalkingCospan (curveGeometricFiberFunctor K Omega x)` and
   produces the certificate field.  The statement is mathematically true (the
   geometric fiber of the scheme pullback of two finite etale covers is the
   pullback of the two fibers); the tree already has the concrete pullback cover
   `finiteEtaleCoverPullbackCover`, its limit cone
   `finiteEtaleCoverPullbackConeInCover` and the limit proof
   `finiteEtaleCoverPullbackIsLimitInCover`, and Mathlib has
   `preservesLimit_of_preserves_limit_cone`/
   `diagramIsoCospan`.  The missing formal step is: the image cone under
   the geometric fiber functor is a limit cone in `Type`, proved with the scheme
   pullback universal property `pullback.lift`/`lift_fst`/`lift_snd`/`hom_ext`.
   No Mathlib object is missing for this item.

3. **preservesFiniteCoproducts -- ISOLATED.** Exact statement:
   `RemainingTypeLevel.preservesFiniteCoproducts`, i.e.
   `PreservesFiniteCoproducts (curveGeometricFiberFunctor K Omega x)`.  Reduces to
   `Fin 2` (binary coproducts) + `Fin 0` (initial) via
   `PreservesFiniteCoproducts.of_preserves_binary_and_initial`.  First missing
   lemma: a morphism from the one-point scheme `Spec Omega` to a binary scheme
   coproduct factors through a summand.  All ingredients exist in Mathlib 4.32.2
   (`Scheme.coprodMk`, `Scheme.isCompl_range_inl_inr`,
   `IsOpenImmersion.lift`, `lift_fac`), the gluing lemma itself is not there.

4. **preservesEpis -- ISOLATED.** Exact statement:
   `Functor.PreservesEpimorphisms (curveGeometricFiberFunctor K Omega x)`.
   Equivalent (epis in `Type` are surjections) to: every epimorphism of finite
   etale covers is surjective on the geometric fiber.  First missing: the
   scheme-side classification "epi iff surjective" for finite etale covers of a
   connected base (field-side analogue `S1747.EpiSurjective` only).

5. **preservesQuotientsByFiniteGroups -- ISOLATED.** Exact statement: for every
   finite group `A`, `PreservesColimitsOfShape (SingleObj A)` of the Type-valued
   geometric fiber functor.  First missing: the quotient of a finite etale cover
   by a finite group action and its universal property (the same G2 gap as
   S2070's `CurveQuotientsByFiniteGroups`, S2072/S2080); even the *existence* of
   the colimit is missing.

6. **reflectsIsos -- ISOLATED.** Exact statement:
   `(curveGeometricFiberFunctor K Omega x).ReflectsIsomorphisms`.  First missing:
   for finite etale covers of the connected curve, "bijective on the fiber at one
   geometric point => iso", which needs local constancy of the fiber cardinality,
   domination of the base by every component, and degree-one finite etale maps
   being isomorphisms.  None of these is in Mathlib 4.32.2.

## 3. What is reusable

* `preservesLimitsOfShape_of_comp_of_reflects` and
  `preservesColimitsOfShape_of_comp_of_reflects` (limits/colimits transfer
  across a fully faithful reflecting functor) -- generic, any `ObjectProperty.lift`.
* `preservesLimitsOfShape_of_typeLevel`,
  `preservesColimitsOfShape_of_typeLevel`,
  `preservesEpimorphisms_of_typeLevel`,
  `reflectsIsomorphisms_of_typeLevel`: the six FintypeCat-valued
  obligations are equivalent to the six Type-valued ones (S2070's layout), so
  any future proof of a Type-valued statement immediately gives the certificate
  field.
* `certificate_of_remaining`: the full six-field certificate from the
  five isolated statements.
* `curveEtaleFundamentalGroupCardV_realized_of_remaining`: consumer combining
  S2081's `s2081_cardV_of_M1_M3` with the certificate, giving
  `Nonempty (CurveEtaleFundamentalGroupCardV K)` from S2080's affine quotient
  input (M1) plus the five isolated statements.

## 4. Technical notes for follow-up work

* Two definitionally equal cover categories coexist:
  `LeanFormal.IUT.Foundations.Geometry.FiniteEtaleCover` (used by
  `geometricFiberFunctor` and by S2070's certificate) and
  `LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations.FiniteEtaleCover`
  (used by the tree's explicit pullback/coproduct constructions).  They are
  `rfl`-equal (S2070 `curveEtaleCoverCategory_eq`) but if both are opened,
  elaboration of `cospan`/`PullbackCone` picks up the wrong one.  An item-2 proof should fix
  one of them explicitly (e.g. an `abbrev Cover` and use it everywhere, or build
  the pullback cover/cone directly in the Geometry category).
* `IsTerminal` (= `IsLimit` of the empty cone) lives in `Type`, not `Prop`: such
  statements must be `def`/`noncomputable def`, not `theorem` (Lean rejects a Type-valued
  `theorem` with "type of theorem ... is not a proposition").
* `PreservesLimit`/`PreservesLimitsOfShape` carry `Nonempty (IsLimit ...)` in this Mathlib,
  use `preservesLimit_of_preserves_limit_cone` to check a single limit cone and
  `isLimitOfReflects`/`isColimitOfReflects` for the transfer.
* `Functor.empty.{0} C` must be universe-pinned in the terminal statements.

## 5. Next executable step

Prove `PreservesLimitsOfShape WalkingCospan (curveGeometricFiberFunctor K Omega x)`
(a homogeneous construction of the pullback cover and its limit cone in
`LeanFormal.IUT.Foundations.Geometry.FiniteEtaleCover`, then the image cone is a limit
cone in `Type` via `PullbackCone.isLimitAux` and the scheme pullback
universal property).  That upgrades item 2 from "isolated" to "proved"; the
other four need new mathematical input listed above.
