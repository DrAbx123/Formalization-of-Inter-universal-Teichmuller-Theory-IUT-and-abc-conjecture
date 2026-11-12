# DECOMP-VOLUME-INEQ — volume inequalities usable for R (A1034)

Status: read-only lemma inventory; no compile.  Sign conventions: `componentVol` is
the normalized Haar **log-volume**; `componentVol_le_of_subset` is monotone
increasing in the set (larger set ⇒ larger log-volume).

## 1. Available monotonicity/containment lemmas

| lemma | statement | source |
|---|---|---|
| `componentVol_le_of_subset` | `S ⊆ T`, `0<haar S`, `haar T<⊤` ⇒ `componentVol S ≤ componentVol T` | `Iut/Wall/Rss.lean:63` |
| `componentVol_mono` | hull regions `a•integralAt ⊆ b•integralAt` ⇒ `componentVol(a•integralAt) ≤ componentVol(b•integralAt)` | `Iut/Concrete/LocalConstruct/Volume.lean:206`, `Theory.lean:222` |
| `leastHull_mono` | `U ⊆ V`, `V` admissible ⇒ `leastHull U ⊆ leastHull V` | `Iut/WallEquiv/Gap.lean:422` |
| `hullAdmissible_mono` | `R≤S` on hull-admissible regions ⇒ `hull R ≤ hull S` | `Iut/Cor312/ContainerHull.lean:95` |
| `le_hullAdmissible` | `R ≤ hull R` (extensivity) | `ContainerHull.lean:90` |
| `packetVol_mono` | hull regions `U⊆V` ⇒ `packetVol U ≤ packetVol V` | `Iut/Concrete/LocalEstimate.lean:430` |
| `processionVol_le_of_packetVol` | pointwise packet inequality ⇒ procession inequality | `Iut/Wall/Rss.lean:172` |
| `logVol_le_logVol_hullOf` | `U⊆S`, both adelic ⇒ `logVol U ≤ logVol S` | `Iut/Wall/Ind3.lean:138` |
| `logVol_le_rhs` | `U ⊆ hullOf(vcI)` ⇒ `logVol U ≤ rhs` | `Iut/Wall/Rss.lean:374` |
| `componentVol_le_leastHull_self` | `U` admissible ⇒ `componentVol U ≤ componentVol(leastHull U)` | `Iut/WallEquiv/Gap.lean:143` |
| `componentVol_integral` | integral region has log-volume 0 | `Volume.lean:201` |

Exact identities (better than inequalities for our decomposition):
- `componentVol_units_smul` (`Iut/Wall/IdentifiedCopies.lean:67`):
  `μ^log(a•X)=μ^log(a•O)+μ^log(X)`;
  with `componentVol_scal...` (`VcI:199-258`) this gives the q-scaling term;
- `componentVol_tensorLogShell_eq` (`VcI:165`):
  `μ^log(⊗𝓘)=shellExcess+orderVol`;
- `componentVol_leastHull_tensorLogShell_eq` (`VcI:603`):
  `μ^log(leastHull(⊗𝓘))=∑_j logShellRadius_j·log p`;
- `ind2Term` definition (`Gap.lean:747`):
  `ind2Term = μ^log(leastHull(thetaComp)) - μ^log(scaleElt•leastHull(shell))`,
  `ind2Term_nonneg` (`Gap:756`);
- `componentVol_arch_scale` (`Volume.lean:252`): `μ^log(t•archBall)=log t`.

## 2. Union subadditivity: not available for log-volume

There is **no** `logVol_union_le`/`componentVol_union_le` in the tree.
Haar measure is subadditive (`measure_union_le`), but `componentVol` is
`log(μ/μ(integral))/n`, and `log(μ(A∪B))` is not `≤ log μ(A)+log μ(B)` in a
useful direction (it is `≤ log(μA+μB)`, and `log` is concave).

Consequences:
- one cannot decompose `R = -vol(thetaHull)` by naive `vol(∪ S_j) ≤ Σ vol S_j`
  and keep nonnegative terms;
- in the theta hull the union is over `indAut` images of scaled shells and is
  **not disjoint**; the extra is measured by `ind2Term`, not by a sum of
  disjoint differences.

## 3. Usable decomposition (exact/one-sided)

At a finite prime for the iv reading:
`thetaHull` component is `leastHull(thetaComponent)`, and
`ind2Term = componentVol(leastHull theta) - componentVol(scaleElt • leastHull shell) ≥ 0`
(`Gap.lean:747-756`).  Hence

`componentVol(thetaHull)
   = componentVol(scaleElt • leastHull(shell)) + ind2Term`

and, using `componentVol_leastHull_tensorLogShell_eq` and the scaling law
`a•shell` (A1023),

`componentVol(thetaHull)
   = ∑_j (ρ_j - k_j)·log p + ind2Term + order/shell corrections`,

with `k_j = j²·ord_p(q_{v_j})/(2ℓ) ≥ 0` (q contraction),
`ρ_j = logShellRadius ≥ 0`; at unramified `ρ_j=0`.

Therefore
`R_finite = -componentVol(thetaHull)
  = ∑_j k_j·log p - ∑_j ρ_j·log p - ind2Term`.

Sign terms:
- `+∑ k_j log p = +∑ j² A_{v_j}`: POSITIVE (the q-scaling that can make R>0);
- `-∑ ρ_j log p`: NEGATIVE or zero (`ρ_j≥0`);
- `-ind2Term`: NEGATIVE or zero (`ind2Term≥0`).

At the archimedean place, `componentVol_arch_scale` gives `log t` terms with
sign depending on the theta scales; `archDefect` (`Gap:459`) is a nonnegative
correction.  Arch sign remains data-dependent.

## 4. What can be proved with existing lemmas

1. `componentVol(thetaHull) ≤ componentVol(scaleElt • leastHull(shell))`?
   Actually `ind2Term≥0` gives the opposite:
   `componentVol(thetaHull) = componentVol(scaled hull) + ind2Term`,
   so `componentVol(thetaHull) ≥ componentVol(scaled hull)`;
   hence `R = -componentVol(thetaHull) ≤ -componentVol(scaled hull)`.
   This is an **upper bound on R**, not a lower bound.
2. From `componentVol_le_of_subset` with `vcI ⊆ thetaHull` (if true) one gets
   `componentVol(vcI) ≤ componentVol(thetaHull)`, again an upper bound on R
   (`R ≤ -componentVol(vcI)`), not the needed `R ≥ 0`.
3. To prove `R ≥ 0` one needs the q-scaling positive term to dominate the
   shell/ind2 negative terms: that is exactly the open `(UB)`/per-capsule
   inequality, not a consequence of union subadditivity.

## 5. Minkowski/submodularity

No `hull(A∪B)` volume submodularity or Brunn-Minkowski lemma is formalized in
the repo.  The hull in use is the least `a•integralAt` hull (`leastHull`), not a
convex-geometric hull; its exact volume is `∑ ρ_j log p` (`VcI:603`).
`componentVol` is monotone but not submodular in general; a Minkowski-type
inequality would be a new development, not an existing lemma.

## 6. Recommendation

- Use the **exact** formulas (`componentVol_leastHull...`, `ind2Term`) rather
  than union subadditivity.
- Decompose `R` as `+∑ j²A_v - ∑ρ_j logp - ind2Term + arch` as in §3;
  only the q term is provably positive; `ind2Term` and `ρ` terms are negative
  contributions.
- Prove `R≥0` only after a quantitative lower bound on the q term versus
  `ρ`/`ind2`/arch; this is the per-capsule inequality, not a measure-theoretic
  subadditivity.
- If a union bound is required, use `componentVol_le_of_subset` with a single
  containing hull region, never a sum over overlapping `indAut` images.
