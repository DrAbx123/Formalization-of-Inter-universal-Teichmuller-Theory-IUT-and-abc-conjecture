# S1314: actual C3 Galois root action on the algebraic closure

Date: 2026-10-30.  Lean file:
[tmp/sheaf/xif/paper/S1314C3GaloisRootActionActual.lean](../../tmp/sheaf/xif/paper/S1314C3GaloisRootActionActual.lean).
EXIT=0; 408 lines; SHA256
C4BB2909E728F73126C2A87DAAF48ACEA61DE970750C3D63FD87E4E418898364.

## Verdict

1. **The paper-faithful C3 root/Galois carrier is the algebraic closure**
   `L = AlgebraicClosure K_v`, not the completion `K_v`.  The source takes a
   `2l`-th root of the q-parameter and forms Kummer classes from N-th roots in
   the algebraic closure; see the evidence below.  The actual action on this
   carrier is `NumberFieldFinitePlace.unitsAlgEquiv place : Gal(L/K_v) -> (L^x =* L^x)`,
   which is exactly the action used by the Kummer construction.

2. **The literal S1304 target does not elaborate.**  The type

   ```text
   Gal(L/K) ->* MulAut (NatRootSystem qUnitAlg)
   ```

   fails because `MulAut` requires a `Mul` instance on `NatRootSystem`, and
   `NatRootSystem value` has no source-defined group structure.  Exact Lean
   error from a literal-target probe (the probe intentionally fails to
   elaborate and is not kept):

   ```text
   failed to synthesize instance of type class
     Mul (NatRootSystem (concreteQUnitAlgebraicClosure I place))
   ```

   The root systems of a fixed q-unit form a torsor over the cyclotomic towers,
   not a group; installing an arbitrary group structure would be fake data.

3. **The well-typed actual object is constructed.**  The file builds

   * `galoisUnitsAction : Gal(L/K) ->* MulAut L^x`, the actual unit action,
     with the q-unit fixed by `unitsAlgEquiv_tateParameterUnit`;
   * `galoisRootsAction : Gal(L/K) ->* Equiv.Perm (NatRootSystem qUnitAlg)`,
     the actual permutation action on the root systems of the fixed q-unit;
   * the root law `(sigma • r).root n = sigma (r.root n)`, the power and
     compatibility laws for the acted-on root system, and the root-motion
     nontriviality criterion;
   * the actual Kummer class `actualC3KummerClass`, the identity
     `kummerClass = rootSystemDiff (roots) (sigma • roots)`, the crossed
     multiplication law, and the change-of-roots coboundary identity.

   The package is `ActualC3GaloisRootAction`.  It is the well-typed
   replacement for the literal `MulAut (NatRootSystem ...)` target.

## Paper evidence

- IUT II, Introduction, p. 2: `q_v` is the q-parameter at `v`, and the source
  chooses `q~_v`, a `2l`-th root of `q_v`.  This root lies in an extension of
  `K_v`, not in `K_v` in general.
- IUT II, Section 3, p. 90: Kummer classes are formed by extracting N-th roots
  of theta values and passing to Galois cohomology classes.
- IUT III, Remark 3.11.4, (ii), p. 173: a Kummer isomorphism is completely
  determined by (a) the cyclotome isomorphisms and (b) the Galois action on the
  roots of the elements of the monoid under consideration.
- IUT III, Definition 3.8, (i), p. 112: the q-pilot object is determined by the
  actual local `q_v`; its Kummer class is the Galois-side object.

Local PDFs:
[mochizuki-iut-ii.pdf](../../tmp/external/promachina-iut-lean/docs/papers/mochizuki-iut-ii.pdf),
[mochizuki-iut-iii.pdf](../../tmp/external/promachina-iut-lean/docs/papers/mochizuki-iut-iii.pdf).

Consequently the old completion-root C3 field is not paper-faithful.  This file
does not construct or fabricate a completion root system.  (The independent
valuation/order no-go for completion roots remains as recorded in S342/S1304;
it is not used as a proof here.)

Source-faithfulness note: `concreteQCandidate` is the actual
`FinitePlaceQCandidate` chosen by the concrete C3 donor, and
`concreteQUnitAlgebraicClosure_eq_tateParameterUnit` only identifies its image
with the `tateParameterUnit` API.  It does not assert that this candidate is the
elliptic curve's Tate parameter; that identification is a separate C3 source gap
(see S1304).  The Galois action and fixed-unit laws hold for any nonzero
completion q.

## Lean construction

Namespace:
`LeanFormal.IUT.XiFPaper.S1314C3GaloisRootActionActual`.

Key declarations:

| Declaration | Role |
|---|---|
| `NatRootSystem.ext` | root-system extensionality |
| `NatRootSystem.mapUnits` | move a root system by a unit equivalence fixing the value |
| `NatRootSystem.mapUnitsEquiv` | the induced bijection of root systems |
| `concreteQUnitAlgebraicClosure_eq_tateParameterUnit` | the concrete q-unit is the Tate parameter unit in L |
| `galoisUnits_fixed` | q-unit fixed under `unitsAlgEquiv` |
| `galoisUnitsAction` | actual rho on `L^x` |
| `galoisRootsAction` | actual permutation action on `NatRootSystem qUnitAlg` |
| `galoisRootsAction_root` | root law |
| `galoisRootsAction_pow_self`, `..._root_one`, `..._root_compat` | root-system laws after the action |
| `ActualC3GaloisRootAction` | unit action + root action + root law + fixed q-unit |
| `actualC3KummerClass` | actual `KummerClass.kummerClass` |
| `actualC3KummerClass_eq_rootSystemDiff` | class = root-system difference |
| `actualC3KummerClass_mul`, `..._diff` | crossed multiplication / root-change laws |
| `galoisRootsAction_ne_one_of_root_ne`, `actualC3KummerClass_component_ne_one_of_root_ne` | nontriviality criteria |

No `sorry`, `admit`, axiom, arbitrary data, or completion root is used.
The only comment occurrences of those words are explanatory.

## Verification

```text
lake env lean -R D:/lean tmp/sheaf/xif/paper/S1314C3GaloisRootActionActual.lean
EXIT=0
```

- `statement_compiles = true` for the corrected actual target
  (`ActualC3GaloisRootAction` and the Kummer/root-change consumers).
- `proof_body_checked = true` (EXIT=0, no `sorry`).
- `kernel_closed = true` for the listed declarations: the axiom probe shows
  only `propext`, `Classical.choice`, `Quot.sound`.
- The literal target `Gal(L/K) ->* MulAut (NatRootSystem ...)` is
  `statement_compiles = false`; this is the exact type obstruction, not a
  missing proof step.
- `target_accepted = false` for the literal S1304 target.  The corrected
  algebraic-closure target is accepted as the paper-faithful object.

## Remaining exact fields

1. **Old completion C3 schema.**  If one insists on the old
   `SourcePilotRegionData` fields, the first missing field remains
   `roots : NatRootSystem (concreteC3QUnit place)` in the completion.  It is not
   constructed here and should not be fabricated.  The paper-faithful repair is
   to state the C3 roots/Kummer/rootChange fields on `L` (or provide an
   explicit L-side variant), which is what this file supplies.
2. **Nontrivial Kummer class.**  The actual class is constructed, but no
   nontrivial Galois element or moving-root witness is constructed.  The
   criterion theorem
   `actualC3KummerClass_component_ne_one_of_root_ne` states exactly what a
   nontriviality witness must supply.  This is the next exact field if the C3
   consumer needs a nonzero class.
3. **Profiniteness.**  The Lean group is the full automorphism group
   `L ≃+*[K] L`; the Krull topology is not used by `unitsAlgEquiv` or by the
   Kummer class construction.  A profinite-topology refinement is a separate
   layer, not a missing field of this algebraic action.

## Consumer and next action

The consumer is the C3 Kummer/root-change layer (and C4/C9 downstream): it needs
an actual `rho` with the q-unit fixed and a root system, which
`ActualC3GaloisRootAction` + `actualC3KummerClass` provide on `L`.  The next
executable step is a target-level decision to replace the completion-root C3
fields by the L-side object; until then the old completion schema remains an
exact gap and must not be closed by wrapping the algebraic-closure roots.