# S1319: actual D6 boundary clause from the concrete Gaussian curve

Status: **EXIT=0**. Lean file:
`tmp/sheaf/xif/paper/S1319OrbicurveClauseActual.lean`
(558 lines, 22974 bytes, SHA256
E32B6209155A4642F2C207A3FEF5BD47F89E2DDFD892BAF65D3621F3E6454AA4).

Compile:

    lake env lean tmp/sheaf/xif/paper/S1319OrbicurveClauseActual.lean

Log: `tmp/sheaf/xif/paper/S1319Compile.log`.

Axioms of every audited declaration: `propext`, `Classical.choice`,
`Quot.sound`. No `sorryAx`, no new axiom, no `PUnit`/arbitrary carrier.

## Constructed actual content

Over the concrete Gaussian arithmetic input of S1280 (Q(i), curve
`E : y^2 + xy = x^3 + 5`), the file constructs:

* the actual projective point set and the actual punctured point set;
* the explicit actual point (1,2), proved nonsingular and different from
  the origin/puncture, hence the punctured point set is nonempty;
* the actual elliptic sign involution `P |-> -P` and its setoid of orbits;
* the coarse quotient `C = X/(+-1)`, its punctured quotient, and the
  actual quotient map `q : X\{O} -> C\{O}`;
* `q` is surjective and nondegenerate: the distinct points (1,2) and
  -(1,2) have the same image, so `q` is not injective and is not the
  identity/terminal cover;
* the actual structure group `SignGroup = +-1`, cusp count 1, and the
  sign-invariance compatibility of `q`;
* the actual exact sequence of the l-torsion Galois representation
  `1 -> ker(rho_l) -> G_{Q(i)} -> rho_l(G_{Q(i)}) -> 1`;
* a full `SourceOrbicurveClause.{0,0,0}`, with rfl-spec lemmas for every
  field and a consumer-facing summary theorem.

Negative controls in the same file: the quotient curve is nontrivial;
the punctured point set has two distinct points; the identity cover fails
the nondegeneracy condition. The terminal constant stack is not used.

## Exact boundary (D6 is not closed)

This is the actual **point-level boundary clause**, not the full D6 stack
object. The cover map is the coarse quotient map of the sign action, not a
scheme-level finite-etale morphism; the coherent sign action, the stack
quotient, and certified etale fundamental groups are not encoded.

The `exactSequence` slot is the actual l-torsion representation sequence.
It is a genuine exact sequence of the concrete curve, but it is **not** the
orbifold fundamental-group sequence
`1 -> Delta_C -> Pi_C -> G_K -> 1`.

The exact remaining D6 source object is frozen as

    S1319OrbifoldPiGap l := Nonempty (S1319OrbifoldPiData l)

where `S1319OrbifoldPiData l` consists of a **nonterminal**
`HyperbolicOrbicurve` over `K` (the `S1319NonterminalFiber` field
explicitly excludes point/terminal fibres), the once-punctured signature,
and `Iut.OrbicurveFundamentalGroupData` for the absolute Galois group. This
is precisely the input that `SourceDefinition31OrbicurveInstance` says
cannot be replaced by the terminal stack.

## Relation to S1280/S1298

No file outside `S1319OrbicurveClauseActual.lean` was modified. S1280
(D3/D4) and S1298 (D5 exact torsion field) are only imported/read. The D6
boundary clause can be integrated now; a full D6 closure still requires the
nonterminal stack + certified orbifold fundamental groups above.
