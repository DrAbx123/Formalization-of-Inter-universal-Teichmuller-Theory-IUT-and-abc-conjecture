# Marginal hull domination: a route that does not assemble local outputs

Date: 2026-10-26. Owner: root, single agent. SHEAF stage 1, exploratory theorem
plus a checked finite-product Lean lemma.

## Task record

- Target node: `n8-c9-final-evaluation-capsule`; consumer: prove the same fixed-`C`
  scalar comparison `Q_C <= h_C` and the associated q-carrier/hull compatibility.
- Locked data: one paper-admissible `C`, its actual output family `P_C`, native
  q-pilot, holomorphic hull, determinant power `M_C`, inverse-`O(-)` reference,
  place/label weights, and signed readout. None is rescaled or replaced.
- Exact files: this note and `C9MarginalHullGate.lean`; source text is the frozen
  `sources/IUT-III.txt` with SHA256
  `822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D`.
- Statement dependencies: Remark 3.9.5(i)-(iii),(vii), Proposition 3.9, and
  Remark 3.1.1; local product hull geometry is already formalized in
  `LocalFieldProductHull.lean`.
- Proof dependencies: none for the geometric lemmas below. Their application to
  the actual IUT q-pilot remains a source obligation, not a Lean field.
- Stop boundary: do not turn a local support criterion into a claim that the
  complete source gate has closed. Update the node only after a source-level
  coordinate comparison has actually been constructed.

## The new criterion

Fix a place `v` and the finite packet-coordinate index `J_v`. Let `K_{v,j}` be
the corresponding local fields. Let `P_{C,v}` be the union of the actual
allowed output regions in `prod_j K_{v,j}`, and define

```text
rho_{v,j} = max { |x_j| : x is in P_{C,v} }.
H_{C,v}   = prod_j { x_j : |x_j| <= rho_{v,j} }.
L_{q,v}   = prod_j { x_j : |x_j| <= |q_{v,j}| }.
```

Assume the closure of `P_{C,v}` is compact and every coordinate projection is
nonzero. These are precisely the hypotheses under which the paper's finite
holomorphic hull is a nonzero `lambda O` product. Then:

```text
L_{q,v} subset H_{C,v}
  iff for every j, |q_{v,j}| <= rho_{v,j}.
```

The maxima `rho_{v,j}` need not come from one common output. For coordinate
`j`, choose any maximizer `x^(j)` of `|x_j|`; the vector
`lambda=(x^(j)_j)_j` is used only as the scaling vector defining the product
hull. It need not itself belong to `P_{C,v}`. This is allowed by the actual
hull definition: the hull is a product `lambda O` containing the union of
regions, and it combines the coordinate maxima. It does not assert that the
algorithm outputs the artificial tuple of those maxima.

Proof. Compactness gives a maximizer of each continuous coordinate norm on the
closure of `P_{C,v}`. Pick one independently for each `j`, and let `lambda_j`
be its `j`-th coordinate. Every `x` in the output union then satisfies
`|x_j| <= |lambda_j|` for every `j`, so the union is contained in `lambda O`.
If `mu O` is any other nonzero product dilation containing the union, the
maximizer for coordinate `j` lies in `mu O`; hence `|lambda_j| <= |mu_j|`.
Thus `lambda O` is the least hull. Now `L_q subset lambda O` implies, by
testing the vector `(q_{v,j})_j` in `L_q`, that each
`|q_{v,j}| <= |lambda_j|`. Conversely those coordinate inequalities imply
every vector in `L_q` lies in `lambda O`. This proves the equivalence.

The argument is not an illicit local-to-global assembly. The hull already is
the product of its coordinate discs. It only uses different outputs to compute
different marginal maxima; it never claims those outputs glue to one global
output.

## Same-normalization scalar consequence

Suppose the fixed source readouts, place by place, have the form

```text
Q_{C,v} = sum_j w_{v,j} ( M_C log |q_{v,j}| + c_{v,j} )
h_{C,v} = sum_j w_{v,j} ( M_C log rho_{v,j} + c_{v,j} ),
```

where `w_{v,j} >= 0`, `M_C > 0` is the same tensor power on both sides, and
`c_{v,j}` is the same inverse-reference/normalization contribution on both
sides. If the coordinate inequalities above hold, monotonicity of `log`,
multiplication by the positive `M_C w_{v,j}`, and finite summation give
`Q_{C,v} <= h_{C,v}`. Summing over the original places with the source's
degree/product-formula convention gives `Q_C <= h_C`, provided the source's
usual support or convergence conditions for those sums are verified.

No actual output needs to have readout `Q_C`; no arbitrary local outputs need
to be assembled; no global q-to-hull morphism is needed for this scalar
consequence. What is needed is still real and source-specific: for every
relevant `(v,j)`, establish the q-radius bound against the projection of the
same fixed-`C` output union, with the same `M_C`, reference, weights, and signed
readout. The scalar conclusion is not assumed in these local inequalities.

If the output union is not relatively compact, Remark 3.9.5(i) sets its hull
to the full ambient packet. The finite-hull argument above is for the finite
readout branch. In the full-ambient branch one must use the source's extended
log-volume convention directly; it must not be silently converted to a finite
radius argument.

## Attempt to derive the local source inequalities

The route is independent of A1/A2/A3 as Lean prerequisites and does not restart
`OriginalInput -> Input`. The paper already gives the following ingredients:

1. Remark 3.9.5(i)-(ii) defines the hull as the least `lambda O` product region
   containing the output region/family. The local finite-product shape is
   exactly the one used in the criterion.
2. Remark 3.9.5(vii), Ob1-Ob4, explains why the output hull is replaced by a
   locally free arithmetic vector bundle and then by `det^M`, with the same
   `O(-)` correction needed to compare to the q-pilot line.
3. Theorem 3.11(iii) and Remark 3.11.1(iii) give full `F^× mu` prime-strip
   isomorphisms between the q-pilot input strip and the intermediate/output
   strips. Remark 3.9.5(ix) asserts that after sQ3/sQ4 the chain closes modulo
   formal quotient indeterminacies while retaining the q-intertwining.
4. cQ3 describes local pullbacks and structure-poly-morphism orbits to the
   determinant hull. If the closed-loop q-intertwining can be evaluated in
   this local category, it should give the required marginal inclusion at
   each `(v,j)` directly. Different local intermediate outputs may be used
   for different coordinates; no overlap cocycle between those witnesses is
   required for the numeric sum.

The proof attempt stops at item 4's exact source content. The cited paper
asserts compatibility, but the present Lean declarations and the checked
source excerpts do not yet exhibit, for a fixed `C`, the local map from the
q-pilot lattice (after `det^M` and the fixed inverse reference) into the
projection of the actual output hull. A prime-strip isomorphism alone is not
that module inclusion; cQ3's structure map alone has an output/hull object as
its source. The new criterion reduces the needed construction to the local
radius inequalities and removes global assembly, but does not itself derive
those inequalities. It is therefore a new sufficient source route, not a
completed C1 proof and not a counterexample to the paper assertion.

The source instantiation must still check: (a) the exact local q-lattice and
its generator up to the allowed unit; (b) that cQ3's pullback gives a map with
the inclusion direction required by the radii; (c) the same determinant power,
inverse reference and weights; (d) all relevant places, including any
archimedean or infinite-support branch; and (e) that the signed local readouts
sum to the locked `Q_C` and `h_C`. If any item fails, this route does not prove
the global inequality.

## Lean check and reuse

`C9MarginalHullGate.lean` proves:

- `region_subset_region_iff`: product-carrier inclusion iff every coordinate
  radius is bounded;
- `exists_marginal_hull_certificate_iff`: under compact closure and nonzero
  coordinate projections, q-carrier inclusion in the least hull iff the
  coordinate inequalities hold;
- `weighted_logReadout_mono`: those inequalities imply the weighted signed
  log comparison with a common nonnegative tensor-power factor and identical
  reference offsets.

The local product hull theorem it consumes already proves that coordinate
maxima can be attained at different points. This Lean result contains no IUT
q-pilot or source-output constructor. `statement_compiles=not_run` for the
paper-specific source statement; `proof_body_checked=not_run` for any IUT
source bridge; `kernel_closed=not_run` for the project target;
`target_accepted=false`. The scratch geometric file was checked separately by
`lake env lean` and compiled with exit 0; no Project build, comparator, or
independent review was run.

## Reuse decision

This replaces the assumption that the only independent route must produce one
fixed q-marked global output or a global localization cocycle. It does not
replace the target `Q_C <= h_C`, does not weaken its quantifiers, and does not
claim the still-missing local source inequalities. Next action: take one fixed
`C` and one place `v`, instantiate the q-lattice and hull projection in the
actual cQ3 category, and derive or refute the coordinate radius inequality
from the `U2 K2`/closed-loop q-intertwining before expanding to other places.
