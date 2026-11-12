# FEAS-PLURIPOTENTIAL — psh/Monge-Ampère feasibility

Status: feasibility analysis; no compile.

External sources:
- arXiv:1805.01016, Spaces of norms, determinant of cohomology and Fekete points in non-Archimedean geometry;
- arXiv:2112.03873 is p-adic adelic metrics and Quadratic Chabauty I, not a determinant/Fekete paper. The mismatch is recorded explicitly.

## 1. What 1805.01016 proves

Relevant formulas:
- vol(norm,norm') := log( det(norm') / det(norm) );
- vol(L,phi,psi) := lim n!/m^(n+1) vol(norm_mphi,norm_mpsi);
- vol(L,phi,psi) = - vol(L,psi,phi);
- vol(L,phi,psi) = E(phi,psi), the relative Monge-Ampère energy;
- det H^0(mL) = m^(n+1)/(n+1)! <L^(n+1)> + ...;
- d/dt vol(L,phi+t f,phi) = integral f (dd^c env(phi))^n.

Setting: L ample on a projective variety over a complete valued field; phi,psi continuous metrics; env is the psh envelope; Fekete points/transfinite diameter.

Monotonicity is for the same L and ordered metrics.

### Consequence of phi <= psi

From phi <= psi, env(phi) <= env(psi) and the relative energy/volume inequality in the direction fixed by the determinant norm; the exact sign is convention-dependent. This is a genuine monotonicity theorem, but about two metrics on one line bundle, not two different q/theta regions/lattices.

## 2. Can our q/theta regions be instantiated?

Objects in our chain:
- local log-shell and tensor log-shells;
- leastHull of a region a·O in an additive tensor product;
- componentVol(S) = log(mu S / mu O)/d on Tensor;
- qroot^(j^2) scaling and ind2Term.

These are additive lattices / Haar measures on finite-dimensional Q_p-vector spaces, not sections of an ample line bundle on a projective variety. There is no Berkovich analytification or model in the tree.

Mapping table:
| paper object | our object | gap |
|---|---|---|
| projective X over complete valued field | none (only tensor/lattice) | no X, no L |
| Berkovich analytification X^an | none | absent |
| continuous metric phi on L | lattice gauge a·O / Haar | local analogue only |
| psh envelope env(phi) | leastHull? | leastHull is a lattice hull, not a psh envelope |
| Monge-Ampère (dd^c phi)^n | Haar measure on tensor | local measure, no MA operator |
| det H^0(mL) / Deligne pairing | determinantNorm rank-one | only rank-one fractional ideal |
| Fekete points/transfinite diameter | none | absent |

Thus a literal instantiation is not possible without constructing a projective model, X^an, metrics, and the determinant-of-cohomology functor.

## 3. Could a local psh/MA model reproduce the target?

One can define a local relative volume for two lattice gauges:
vol(phi_a, phi_b) = log(mu(a·O)/mu(b·O))/d.

Monotonicity a·O subset b·O gives vol(...) <= ..., exactly componentVol_le_of_subset. This is already formalized (Haar/lattice monotonicity). It does not yield -A <= -R unless one also identifies a·O/b·O with q/theta regions and proves containment; that is the same gap as Mzk1QRegionInclusionActual, not a new theorem.

The target needs one of:
1. region inclusion theta subset q plus signed volume identities;
2. line-bundle/determinant comparison globalLogVolume det <= globalLogVolume q;
3. psh potential inequality phi_q <= phi_theta on the same line bundle, plus the relative volume sign convention.

(3) is the pluripotential restatement; it is only useful if the psh potentials are actual objects and the comparison is not the desired inequality in disguise.

## 4. Judgment A/B/C

A — feasible now with green assets: only abstract monotonicity (haarLogVolume_mono, componentVol_le_of_subset, signed/negative-log monotonicity, Mzk1QRegionInclusionActual). Not the target inequality.

B — feasible with new definitions, conditional: a local non-Archimedean psh/lattice model, define lattice gauges and relative volume, prove a·O subset b·O => vol(a,b) <= 0, then state theta subset q as a hypothesis. This is a repackaging of Haar monotonicity, not a new lower bound unless it also supplies the region identification.

C — not feasible now: the global determinant-of-cohomology/Fekete/MA theory needed for the literal 1805.01016 comparison: Berkovich spaces, Chambert-Loir measures, Deligne pairings, ample models, Fekete theory. None is in Mathlib/LeanFormal.

Verdict: C for the literal pluripotential route; B only as a restatement; A does not reach the target.

## 5. Mapping if one formalizes a local model

| target step | pluripotential analogue | must build |
|---|---|---|
| q/theta region | lattice gauge a·O / metric phi | lattice-gauge def; no X |
| inclusion theta subset q | phi_q <= phi_theta on same bundle | same-bundle identification |
| volume comparison | vol(L,phi_q,phi_theta) sign | relative volume def + sign convention |
| -A <= -R | signed volume inequality | A/R normalization identities |
| ind2Term | MA mass of hull enlargement | MA operator/Chambert-Loir measure |

## 6. Required new definitions / literature

1. Berkovich analytification X (or a local skeleton model);
2. continuous/psh metrics on a line bundle, psh envelope env;
3. relative volume vol(L,phi,psi) and its monotonicity;
4. Monge-Ampère measure (dd^c phi)^n (Chambert-Loir);
5. determinant of cohomology/Deligne pairing;
6. Fekete points/transfinite diameter (optional for the inequality).

Literature: 1805.01016 (main); Chambert-Loir–Ducros for non-Archimedean forms; Deligne pairings. 2112.03873 is unrelated (Quadratic Chabauty).

## 7. Recommendation

- Do not replace the current region/line-bundle route by a pluripotential restatement: it would be circular or require C-level porting.
- Use 1805.01016 only as normalization/reference for determinant volume formulas (vol = log det ratio), not as a source of the q/theta inequality.
- Keep the concrete tasks: Form C arithmetic (green), theta subset q/volume identities (GAP), and the ported declaration build.
