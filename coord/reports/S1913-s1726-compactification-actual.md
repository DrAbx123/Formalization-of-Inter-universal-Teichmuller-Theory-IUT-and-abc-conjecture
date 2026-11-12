# S1913: the actual S1726 compactification — precise first missing, and the conditional cusp

Status: **proof file compiled** (EXIT=0, no error, no warning, axioms trio only,
no `sorryAx`).  Result type: **missing** — the exact first missing is named and
the boundary cusp is *constructed from it*, but the compactification scheme and
the non-identity representable open immersion are not in the tree and are not
fabricated.

## Deliverable

| item | value |
|---|---|
| file | tmp/sheaf/xif/paper/S1913S1726CompactificationActual.lean |
| lines | 249 |
| source bytes | 13560 |
| source SHA256 | 423A9922A9B211E7AE37F93514F2E17420165EEB48EBF7E75365803821479C1E |
| compile | `lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1913S1726CompactificationActual.olean tmp/sheaf/xif/paper/S1913S1726CompactificationActual.lean` |
| EXIT | 0 (no error, no warning) |
| olean | .lake/build/lib/lean/tmp/sheaf/xif/paper/S1913S1726CompactificationActual.olean (139576 bytes, 2026-11-01T14:43:10) |
| olean SHA256 | E7457EDA20347893F12FFDF5BFEFE29F71B3792730A7546429208DFB44750AEB |
| axioms | propext, Classical.choice, Quot.sound only (6 `#print axioms` checks, all public declarations) |
| sorry/admit/axiom in code | none (grep; the words appear only in doc comments) |

## What is constructed (unconditional)

1. **The precise scheme-level compactification datum**
   `S1913AffineCompactification`: a scheme over `F'`, an open immersion of the
   actual affine Weierstrass model `S1726AffineOver`, density of its image, a
   proper structure morphism, a point at infinity `S1726Base ⟶ scheme`, and the
   separation `∀ s, s ≫ openMap ≠ pointAtInfinity`.

2. **The compactification stack**
   `S1913CompactificationStack C`: the representable etale stack of the
   compactifying scheme; the stack condition is proved
   (`S1913RepresentableIsStack` for every scheme over `F'`).

3. **The stack open map and the boundary point**
   `S1913StackOpenMap C = S1742StrongTransOfHom C.openMap` and
   `S1913BoundaryPoint C = S1742StrongTransOfHom C.pointAtInfinity`, with the
   2-Yoneda computation rules `S1913StackOpenMap_app` and `S1913PointObject`.

4. **The boundary separation is proved, not assumed**
   `S1913Boundary_isBoundary`: at the residue scheme `Spec F'`, no point of the
   orbicurve maps to the point at infinity.  The proof uses only the
   scheme-level separation field and the 2-Yoneda formulas, hence the S1896
   obstruction (identity is essentially surjective at the residue scheme) is
   genuinely avoided.

5. **The boundary cusp, conditional exactly on the representable open
   immersion**
   `S1913BoundaryCusp C (h : EtaleStackOpenImmersion C.S1913StackOpenMap)` and
   `S1913Cusp_of_compactification` / `S1913Cusp_of_inputs`.

6. **Non-degeneracy** `not_isIso`: if the open immersion were an isomorphism,
   the point at infinity would be the image of a point of the affine model.
   Hence a datum strictly extends the affine model; the disjoint-union type
   fake is excluded by density and properness.  This is the scheme-level shadow
   of the S1896 identity obstruction.

## The exact first missing

The first missing datum is `S1913FirstMissing = S1913AffineCompactification`,
i.e. the **projective closure of the actual affine Weierstrass model of E' over
F'** together with the affine chart and the point at infinity:

* the projective closure `P` of `y^2 = x^3 + (61/64) x^2 - (125/64) x` over
  `F'` (a proper scheme over `Spec F'` containing `Spec R'` as a dense open
  subscheme),
* the open immersion `Spec R' ⟶ P`,
* the point at infinity `O = (0:1:0) : Spec F' ⟶ P`,
* the separation `O` is outside the affine chart.

The tree has no such scheme.  The analogous frozen card
`Example36CurveScheme.CurveProjectiveClosureCard` records exactly this gap for
`y^2 = x^3 - x`; it has no inhabitant and no consumer.  (The card's comment
claims Mathlib has no `Proj` scheme API, but this checkout *does* provide
`AlgebraicGeometry.Proj`; I verified the import.  So the projective closure is
constructible in principle from the graded homogeneous coordinate ring, or by
gluing the `Z != 0` and `Y != 0` affine charts along their overlap.  Nothing of
the sort exists in the tree and none is faked here.  Availability of the API is
verified by the probe `tmp/sheaf/xif/paper/_S1913ProjProbe.lean` (EXIT=0):

    #check @AlgebraicGeometry.Proj
    #check @AlgebraicGeometry.Proj.awayι
    #check @AlgebraicGeometry.Proj.toSpecZero
    #check @AlgebraicGeometry.Proj.basicOpenIsoSpec
    #check @AlgebraicGeometry.Proj.affineOpenCover
)

The second input, purely 2-categorical, is
`S1913RepresentableOpenImmersion C`: the representable open immersion of the
induced map of representable etale stacks.  It is the non-identity analogue of
`S1896IdentityOpenImmersion`.  The base change at a scheme point
`t : T ⟶ P` must be the actual schematic fibre product `T ×_P Spec R'`, with a
full `TwoPullbackWitness`; at the identity point of S1896 the apex is the test
scheme itself, which is why the identity case was free.  The tree records the
general-cospan iso-comma stack construction as missing in S1864 (its items
(a)-(d)).  For *representable* stacks the required witness is a pointwise
construction from the scheme fibre product (the 2-image of a scheme pullback
square), but it is not in the tree either.

## Honest boundary

This is **not** an unconditional construction of `OrbicurveBoundaryCusp
S1726Orbicurve`.  The two inputs above are named as a type and a proposition;
neither is assumed, and no fake compactification, `True`, `PUnit`, `sorry`,
`admit` or new axiom is used.  What is proved is that the *only* remaining
geometric datum for the actual S1726 cusp is the projective closure, and that
the boundary separation and the cusp construction are complete once it exists.

## Consequence for the C_K compactification template

The same two-step template applies to `C_K`:

1. construct the actual proper curve compactification of the relevant
   orbicurve (the missing scheme-level input), and
2. construct the representable open immersion of the induced stack map
   (non-identity base changes are scheme fibre products).

Then the boundary argument of `S1913Boundary_isBoundary` goes through verbatim
whenever the source stack is representable.  For the D9 K-core `S.cK` (signature
`(1,l-tors)^±`, S1887 shows it is not `S1726Orbicurve`) the stack is not
representable, so step (2) additionally needs the general iso-comma stack
construction of S1864, not only the schematic fibre-product case.
