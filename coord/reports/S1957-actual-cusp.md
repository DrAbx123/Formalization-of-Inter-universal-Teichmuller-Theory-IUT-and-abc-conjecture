# S1957: the actual boundary cusp Nonempty (OrbicurveBoundaryCusp S1726Orbicurve) is unconditional

Date: 2026-11-01.  Task: import S1946 + S1947 + S1926, take
`hdom := S1947_isDomain_W` to obtain the *actual* `S1913AffineCompactification`, and apply
S1926 to obtain the *actual* `Nonempty (OrbicurveBoundaryCusp S1726Orbicurve)`; or report
the exact first missing.  No fake cusp, no new hypothesis, no change of objects.

## Result (short)

**EXIT=0.  The D9 boundary cusp of the actual S1726 orbicurve is a theorem, with no missing
datum left in this chain.**  Zero errors, zero warnings, no `sorry`/`admit`/`axiom`, and
`#print axioms` on every probed declaration prints only
`[propext, Classical.choice, Quot.sound]`.

    tmp/sheaf/xif/paper/S1957ActualCuspActual.lean
    SHA256 3ED4F68C848708CB0F96F557D0360BE077E397F7653BBE3A5DE6516357CE9306
    (7627 bytes)

    olean .lake/build/lib/lean/tmp/sheaf/xif/paper/S1957ActualCuspActual.olean
          (22392 bytes, SHA256 3F61335E05A8D7FCE6165C548A1A4355790485953462D97865AE1FA6C93F486E)

Compile (project convention, emits the olean):

    lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1957ActualCuspActual.olean \
        tmp/sheaf/xif/paper/S1957ActualCuspActual.lean
    EXIT=0, ELAPSED=45.2 s, no diagnostics.

The same file also typechecks without `-o` (`lake env lean ...`, EXIT=0).

## The assembled objects

* `S1957Compactification : S1913AffineCompactification`
  `:= S1946Compactification_of_domain S1947_isDomain_W`.
  This is a **closed** declaration: `#check @S1957Compactification` prints exactly
  `S1957Compactification : S1913AffineCompactification`, i.e. the `[GradedRing (CohomGr Wang)]`
  argument of `S1946Compactification_of_domain` is discharged by the global instance
  `S1936GradedRingWang` (reached through S1947's import of S1936), and the `IsDomain W`
  argument is discharged by S1947.  No hypothesis remains.

* `S1957ActualCusp : Nonempty (OrbicurveBoundaryCusp S1726Orbicurve)`
  `:= S1926Cusp_of_compactification S1957Compactification`.

Designation of the actual objects (all by `rfl`, i.e. definitional, not asserted):

* `S1957Compactification_eq_S1937` :
  `S1957Compactification = S1937AffineCompactification S1946ChartAlgEquiv
     (S1937DenseChart_of_domain S1947_isDomain_W)`.
  The datum is S1937's own construction from the S1946 chart identification and the S1947
  density of the affine chart.
* `S1957Compactification_scheme` : `S1957Compactification.scheme = Over.mk S1937ProjHom`.
  The compactifying scheme is the projective closure `Proj WGr` of the affine Weierstrass
  model (with structure morphism `Proj.toSpecZero WGr` composed with the degree-zero
  identification) -- not a disjoint union or a fabricated carrier.
* `S1957Compactification_pointAtInfinity` :
  `S1957Compactification.pointAtInfinity = S1937BoundaryPoint`, the point at infinity
  `O = (0:1:0)`, proved outside the affine chart (`S1937_separation`).

The remaining fields are the S1937 theorems, not inputs: `openImmersion`
(`S1937OpenMap_isOpenImmersion`), `dense` (`S1937DenseChart_of_domain S1947_isDomain_W`),
`proper` (`S1937_isProper`).

## The S1926 input at this datum

* `S1957RepresentableOpenImmersion : S1913RepresentableOpenImmersion S1957Compactification`
  `:= S1926RepresentableOpenImmersion S1957Compactification`.
  S1913's second input is a theorem: the base change of the compactification map at every
  scheme-valued point is S1926's actual scheme fibre product `S1926PullbackScheme`, with the
  two-pullback witness `S1926TwoPullbackWitness` instantiated from S1911.

* `S1957ActualCusp_via_inputs` re-derives the same cusp through the literal two-input form
  `S1913Cusp_of_inputs S1957Compactification (S1926OpenImmersion S1957Compactification)`.

The cusp is therefore S1913's own `S1913Cusp_of_compactification` applied to the projective
closure datum; no cusp witness, compactification or 2-categorical cell is postulated.
Nothing in the file is a hypothesis on the target: the only section variables of the three
sources were `[GradedRing (CohomGr Wang)]` (global instance S1936) and `IsDomain W` (S1947).

## Verification

* source SHA256 3ED4F68C848708CB0F96F557D0360BE077E397F7653BBE3A5DE6516357CE9306;
* `lake env lean -j1 -o ...` EXIT=0 (~45 s), no warnings/errors/sorryAx;
* consumer probe `tmp/sheaf/xif/paper/_S1957Consumer.lean` **imports the emitted olean**
  (EXIT=0, ~49 s) and re-checks, in a fresh module, the exact target statements
      `example : S1913AffineCompactification := S1957Compactification`
      `example : Nonempty (OrbicurveBoundaryCusp S1726Orbicurve) := S1957ActualCusp`
      `example : S1913RepresentableOpenImmersion S1957Compactification :=
        S1957RepresentableOpenImmersion`
  then `#print axioms S1957ActualCusp` = `[propext, Classical.choice, Quot.sound]`;
* axiom audit inside the source on all eight declarations: axioms trio only;
* lexical scan: no `sorry`, no `admit`, no `axiom`, no `native_decide`.

## Status of the former residuals (all discharged, none assumed)

| residual | discharged by |
| --- | --- |
| chart identification `S1937ChartAlgEquiv` | S1946 (`S1946ChartAlgEquiv`) |
| density of the affine chart `S1925DenseChart` | S1947 (`S1947_isDomain_W`, `S1947DenseChart`) |
| representable open immersion `S1913RepresentableOpenImmersion` | S1926 |
| graded-ring structure `GradedRing (CohomGr Wang)` | S1936 (`S1936GradedRingWang`, global instance) |
| scheme-level compactification `S1913AffineCompactification` | S1937/S1946 applied to the above |

The scheme-level datum consumed by S1926 is the projective closure of the S1726 affine
Weierstrass model and the cusp is its boundary point at infinity, so the D9 cusp is realized
by an actual compactification rather than by a label.

## Notes for integration

`coord/STATE.md` and `coord/queue.md` were not modified by this packet (they are stale for
this whole batch as of 15:04; recent packages S1946/S1947/S1926 recorded their results as
reports here instead).  `coord/` is untracked in git, so this report adds no tracked diff.
