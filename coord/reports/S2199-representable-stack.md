# S2199: representable IsStack CLOSED; remaining nondegeneracy + curve points

Date: 2026-11-02. Layer: **O** (source orbicurve D6). No target change,
no fake, independent of 3.11/Eta.

## Audit correction

S2193 reported the representable-fiber `IsStack` as missing. That was too
strong: the tree already contains the explicit bridge

```text
Iut.N8Closure.RepresentableStackIsStackConstructed.representableEtalePresheaf_isSheaf
Iut.N8Closure.DiscreteSheafIsStack.discretePseudo_isStack
```

The first proves the representable presheaf is a sheaf for the big etale
topology; the second proves the discrete-category pseudofunctor of a
type-valued sheaf is an etale stack. S2199 applies them, so
`IsStack` for `schemeRepresentableEtalePseudofunctor F X` is now actual.

## Files read

- `tmp/sheaf/xif/paper/S2193D6RealizationModelActual.lean`
- `tmp/sheaf/xif/paper/S1419D6NonterminalStackActual.lean`
  (`DiscreteSheafStack.discretePseudo_isStack` and the sheaf bridge)
- `tmp/sheaf/n8/closure/RepresentableStackIsStackConstructed.lean`
- `tmp/sheaf/n8/closure/DiscreteSheafIsStack.lean`
- `Iut/Foundations/Orbicurve.lean`
- `tmp/sheaf/xif/paper/S2188D6RealizationActual.lean`
- reports `S2193-d6-stack-model.md`, `S2188-d6-realization.md`

## Deliverable

`tmp/sheaf/xif/paper/S2199RepresentableStackActual.lean`

```text
EXIT=0
olean=YES
lines=92
SHA256=A5D962B9BB6DF171F6BCC17693F3347F9C1CE68CFA7A2677CAF958B567A3E3E1
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2199RepresentableStackActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT / PROVED (actual)

1. `s2199_representable_isStack F X`:
   `(Iut.schemeRepresentableEtalePseudofunctor F X).IsStack
      (Iut.SchemeOverField.etaleTopology F)`.
   Proof: representable presheaf is a sheaf + discrete-sheaf-to-stack bridge.
2. `s2199_s2193RepresentableIsStack F X`:
   the S2193 obligation is closed; the candidate fiber is definitionally
   `schemeRepresentableEtalePseudofunctor F X`.
3. `s2199RepresentableStack F X`: actual `S2193RepresentableStack F`
   for every scheme over F, with the IsStack field supplied.
4. `S2199D6Remaining A`:
   `scheme : SchemeOverField A.F`,
   `nondegenerate : ¬ IsPointFiber (schemeRepresentableEtalePseudofunctor A.F scheme)`,
   `curvePointRealization`:
   `∃ f : (schemeRepresentableEtalePseudofunctor A.F scheme).obj
       (LocallyDiscrete.mk (Opposite.op (baseSchemeObject A.F)))
       → A.curve.curve.toProjective.Point, Surjective f`.
5. `s2199D6RealizationOfRemaining`: such remaining data gives the actual
   `S2188D6Realization A`; `isStack` is now a theorem.
6. `S2199D6RemainingRequired A := Nonempty (S2199D6Remaining A)`,
   with definitional iff.

No inhabitant of `S2199D6Remaining` is asserted.

## Exact remaining first missing

```text
S2199D6Remaining A
  = scheme : Iut.SchemeOverField A.F
  × nondegenerate :
      ¬ IsPointFiber (schemeRepresentableEtalePseudofunctor A.F scheme)
  × curvePointRealization :
      ∃ f : (schemeRepresentableEtalePseudofunctor A.F scheme).obj
            (LocallyDiscrete.mk (Opposite.op (baseSchemeObject A.F)))
            → A.curve.curve.toProjective.Point,
        Function.Surjective f
```

The `IsStack` part is no longer missing.

## Why the remaining data is not constructed

- `nondegenerate`: `IsPointFiber` is a strong all-test-scheme
  subsingleton condition; it must be disproved by an actual non-point value of
  the representable functor. The terminal/point fibers are excluded, but no
  actual scheme-over-F with the required non-point value is selected and
  proved.
- `curvePointRealization`: a surjection from the `F`-points (sections
  `Spec F -> X`) of the chosen scheme onto the projective points of the actual
  punctured elliptic curve `A.curve` is not constructed. In particular, the
  affine Weierstrass scheme need not realize all projective points; an actual
  projective/root-stack model is required.
- No quotient-stack model over `SchemeOverField F` is constructed; S2057's
  finite root-stack groupoid is not an `EtaleStackPseudofunctor F` and has no
  bridge to it.

No fake nondegeneracy or curve-point map is introduced.

## Consumer

An inhabitant of `S2199D6Remaining A` gives
`s2199D6RealizationOfRemaining : S2188D6Realization A`, hence
`S2177ActualD6Orbicurve A`, `xF`/`xF_geometry`, and the
`SourceSignQuotientData` prefix. Independent of 3.11/Eta.

## Next executable subgoal

```text
choose an actual scheme X over A.F
and prove:
  ¬ IsPointFiber (schemeRepresentableEtalePseudofunctor A.F X)
  ∧ ∃ surjection from X-points at Spec A.F onto A.curve projective points
```

The `IsStack` theorem is discharged.

## Reports read

`coord/reports/S2193-d6-stack-model.md`,
`coord/reports/S2188-d6-realization.md`, plus the S1419 discrete-sheaf stack
and representable-sheaf bridge.
