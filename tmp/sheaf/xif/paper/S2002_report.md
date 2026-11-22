# S2002 report: the l-tors root stackification — exact first missing

Date: 2026-11-01.  File: `tmp/sheaf/xif/paper/S2002RootStackificationActual.lean`.

## Verdict

The root stackification `S1997RootStackification K l` is **not** constructed.
The file isolates the exact first missing datum, proves the surrounding
reductions, and proves that the missing datum cannot be supplied by the stack
machinery currently in this tree (all of which produces stacks with *discrete*
fibers).

## What is proved (all unconditional, kernel-checked)

1. `isStack_of_isPrestack_and_essSurj` (general, arbitrary site): a
   Cat-valued prestack with effective descent for every covering sieve is a
   stack.  Mathlib only has the converse (definition of `Pseudofunctor.IsStack`).
2. `S1997RootPrestack_isStack_iff`: for the root prestack,
   `IsStack J <-> IsPrestack J and S1997RootEffectiveDescent K l`
   (the two halves of Mathlib's definition of a stack).
   Consequently `S1997RootStackification_of_prestack_descent`: prestack +
   effective descent solves the whole S1997 missing datum (identity comparison),
   and `S1997RootEffectiveDescent_of_isStack`: effective descent is necessary.
3. `S2002_noFaithfulAtOrigin_of_discreteFiber` (no-go): if all hom types of a
   pseudofunctor `Q` are subsingletons then no comparison
   `S1997RootPrestack K l -> Q` can be faithful at the origin, because the
   order-`l` origin automorphism is killed.  Hence every witness stack is
   genuinely stacky.  `S2002_witness_not_discreteFiber` is the same statement
   for a witness of the S1997 structure.
4. `S2002RepresentableDiscreteFiber` + `S2002_noRepresentableWitness`: every
   representable etale stack has discrete fibers, so **no representable etale
   stack can be the root stackification**.  The tree's other stack construction
   (discrete sheaf stack, S1419/S1421) is also discrete-fibered, so the same
   no-go applies: the missing input is not obtainable from the existing stack
   machinery.
5. `S2002_witness_aut`: any witness carries the origin automorphism to a
   nontrivial order-`l` automorphism of the image point; `S2002_witness_end_nontrivial`:
   the endomorphism type at that point is not a subsingleton.
6. `S2002RootHom_isIso` (via `S2002RootHomInv`), `S2002RootGroupoid`,
   `S2002RootPrestack_pointwise_groupoid`: the root prestack is groupoid-valued,
   so its stackification is a DM-type stack and not a sheaf of sets.
7. `S2002RootStackificationDatum` + `S2002RootStackificationDatum_iff`: the
   missing datum written as an existential over test stacks is exactly S1997's
   structure.  `S2002RootStackificationDatum_implies_S1994`: it still gives
   `S1994StackyOrbicurveMissing`.
8. `S2002LocalRootDatum`, `S2002CanonicalLocalRootDatum`: the
   local-trivialization shape of stackification objects over a test scheme
   (covering sieve + root descent datum), with the tautological object-level
   comparison.  Explicitly **not** claimed to be a stack.

## Exact first missing

```
S2002RootStackificationDatum K l  :=
  exists (Q : EtaleStackPseudofunctor K) (_ : Q.IsStack (etaleTopology K))
    (e : StrongTrans (S1997RootPrestack K l.value) Q),
    forall f : End (S1997CyclicOrigin K l),
      (e.app (cyclic point)).toFunctor.map f = id -> f = id
```

Mathematically this is the quotient stack `[Z / mu_l]` with
`Z = Spec K[t]/t^l`, `mu_l = Spec K[t,t^{-1}]/(t^l-1)`, `zeta . b = zeta*b`:
objects over `U` are `mu_l`-torsors `P` on the etale site of `U` with a
`mu_l`-equivariant map `P -> Z`; over affine `U` these are, up to dualizing
conventions, `(L, phi : L^{tensor l} = O_U, s in Gamma(U, oplus_{i<l} L^{tensor i}))`
with `s^l = 0`.  The comparison sends `b` to the trivial torsor.

## Missing infrastructure (none of it is in Mathlib v4.32.2)

1. `G`-torsors on a Grothendieck site for a sheaf of groups `G`
   (here the representable group scheme `mu_l`) and their descent;
2. the associated twist `(P x Z)/G` and the stack of equivariant maps;
3. effective descent (`Pseudofunctor.IsStack`) for that quotient stack;
4. the comparison and its origin-faithfulness (formal once 1-3 exist).

Point 3 is real mathematics, not a Lean gap: for `K` containing a nontrivial
`l`-th root of unity a Kummer cover (e.g. `l`-th power on `G_m`, or the
`mu_l`-Galois algebra `K[T]/(T^l-a)`) yields a non-effective descent datum
(`b = 0` locally, transition units the nontrivial `mu_l`-cocycle of the cover,
which is not a coboundary because every `mu_l`-valued unit on the cover is
constant).  So `S1997RootEffectiveDescent` is expected to **fail** and the
prestack route is only a sufficient condition.  This Kummer computation is not
formalized in this file and is flagged as such in the docstring.

## Evidence

- Build: `lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2002RootStackificationActual.olean tmp/sheaf/xif/paper/S2002RootStackificationActual.lean`
- EXIT=0, no warnings, no `sorry`/`admit`, no new axioms.
- Source: 367 lines, 20810 bytes, SHA256 4C4CFEBDB775D9F01A38F23AB0DF4B8A5F21FCDC2CB9CA7000EDA6A5B6571B78.
- Olean: 331464 bytes, SHA256 3FBF042F49EFE83F417F319FC52FA36AD5FD6BB6377995963693E5A79A9F538C.
- `#print axioms` for every declaration: only `propext`, `Classical.choice`, `Quot.sound`.
- Repo HEAD 9399e9fab4d62ea5f78a4a0d56ceecb84525a3ee; Lean 4.32.2.

## Consumer and next step

Consumer: S1994 `S1994StackyOrbicurveMissing` (through S1997), and S1997's
missing datum itself.  Next executable step: implement the stack of
`mu_l`-torsors on the etale site (torsor + descent) and the associated twist;
that is the single missing construction.  A cheaper intermediate: prove
`IsPrestack` for `S1997RootPrestack`, which would leave exactly
`S1997RootEffectiveDescent` as the residual half of `IsStack`.
