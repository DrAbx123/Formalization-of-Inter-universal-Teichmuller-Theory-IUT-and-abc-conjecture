# ETA nondegeneracy derived, not guarded

- date: 2026-10-24
- basis: `C9-ETA-FAILED-ROUTES-ADVICE-20261024.md` §5–6,
  `coord/IUT-ROUTE-ETA-V2.md`, and the current guard files.
- Lean changes: **none**. This note retracts unsourced targets and states the
  derived route.

## 1. Withdraw the unsourced guards

The following are **not** valid generic requirements on every source input and
must be removed from the target:

| withdrawn guard | why it is unsourced |
|---|---|
| `Theta != 0` | The reference-region normalization is legitimately zero. A hull/readout of a correct source region may also be zero. Nonzero must be derived from a specific actual region with a different mass, not assumed. |
| `reference != region` | The reference is fixed by the integral structure; the region may equal it. On the reference itself the readout is zero by construction. This is not a defect. |
| type separation `LinesSeparated := not Nonempty (Rval = Rss)` | Different wrappers/types do not express incompatibility. The same underlying real line can carry different specified constructions/coordinates; different wrappers can hide the same constant map. |
| generic `Values != {0}` | Values must be the actual image of varying admissible regions. If the current “Rss/readout” is a fixed-shell singleton, `{0}` is a consequence of the object, not a guard to forbid. |
| generic `comparison nonconstant` | Nonconstancy is a consequence of an actual linear isomorphism plus a nonzero pilot, not a free condition on an arbitrary map. |
| `EtaRemainingGuards` / `EtaComparisonNonconstantRequirement` fields | They quantify arbitrary `Rval`, `Rss`, `theta`, `values`, `reference`, `region`, `comparison` and assert the desired properties. That is a free guard, not a construction. |

In particular, the guard files must not be used to “rescue” a degenerate
readout: a zero readout on a reference region is mathematically correct; the
error is treating a fixed-shell record as the varying `Rss` line.

## 2. What should be derived, and from what

### 2.1 Actual varying `Rss`

`EtaRssLogShellLine.lean:44` fixes `shell`, `volumeIndex` and `logVolume`.
Two elements therefore agree by proof irrelevance; the type is a subsingleton
and every map into it is constant. It is a **fixed-shell record**, not an
`Rss` real line. It must be demoted to a donor/record.

The corrected `Rss` must be the source volume container: actual admissible
regions `R` modulo the source relation of equal volume (or an equivalent
actual varying-region construction). Then:

- non-subsingleton is proved by exhibiting two actual admissible regions with
  different volume (not by a type-level `Nontrivial` assertion);
- the readout `nu_O(R) = (log mu(R) - log mu(O))/d` must descend to the
  quotient and be compatible with the real-line structure;
- the reference `O` is fixed by the integral structure and is independent of
  the variable `R`.

### 2.2 Nonconstancy from an actual linear isomorphism + nonzero pilot

Suppose the actual construction supplies:

```text
eta : Rval -> Rss
```

together with actual `Rval`-addition and `Rss`-addition and a proof that
`eta` is a linear isomorphism of one-dimensional real lines
(`eta 0 = 0`, `eta (x + y) = eta x + eta y`, bijective). Suppose the actual
pilot `p : Rval` satisfies `p != 0`. Then:

```text
eta 0 = 0,      eta p != 0,
```

so `eta` takes two different values and is therefore **not constant**. This
derives the comparison nonconstancy; it does not assume it.

For two independent linear maps `f g : Rval -> Rss` on the same one-dimensional
real line, equality at one nonzero pilot `p` is enough to prove `f = g`:
write any `x = c • p` and use linearity. This is the correct replacement for a
blanket ban on pilot-level comparison: the error is not comparing at the pilot;
the error is naming an arbitrary fixed-point condition “comparison” without
constructing both maps.

### 2.3 Theta / Values from actual regions, not from a guard

Let `O` be the actual reference region from the integral structure and `R` an
actual admissible region with positive finite masses. The local readout is

```text
nu_O(R) = (log mu(R) - log mu(O)) / d.
```

For `R = O` this is zero, correctly. For `R != O` with
`mu(R) != mu(O)` and both masses positive finite, log injectivity on positive
reals gives `nu_O(R) != 0`. Thus Theta nonzero is derived from a specific
actual region with a different mass, not assumed for all inputs.

Likewise `Values` is the image of `nu_O` over the actual varying admissible
regions. It is nondegenerate when at least one such region has a different
normalized volume; it is not a stored singleton or `{0}`. The current actual
finite F-place readout with closed/open unit balls is a valid **local instance**
of this derivation, not a generic guard.

### 2.4 Actual q calibration

The correct q-side input is the actual region action `qO`/packet diagonal and
the local Haar scaling formulas:

```text
mu(qA) = m_K(q) mu(A),
nu_O(qO) = log m_K(q) / d,
nu_O(qI) = log m_K(q) / d + log N / d,
nu_I(qI) = log m_K(q) / d.
```

These derive the q-region readout from actual multiplication and shell/index
data. They do not set a fixed shell discrepancy equal to q, and they do not
force the unit-part log `log(u)` to be nonzero: for `q = pi^n`, `u = 1` and
`log u = 0`, while the valuation/region action is nontrivial.

## 3. Old guard files: disposition

### Archive (negative control, do not consume)

- `tmp/sheaf/n8/closure/EtaNondegeneracyGuards.lean` — entire file. Its
  `LinesSeparated`, `IntegralStructureProper`, `ThetaNonzero`,
  `ValuesNondegenerate`, `RefRegionSeparated`, `ComparisonNonconstant` are
  generic props on arbitrary parameters, and the named gap asserts the bundle
  for arbitrary data. Currently not green; archive without repair.
- `tmp/sheaf/n8/closure/EtaNondegeneracyActual.lean` — archive the
  `EtaRemainingGuards` structure and `etaRemainingGuards_gap`. Retain only
  `EtaNondegeneracyActualCore` (actual `EtaValueGroupLineData`,
  `EtaRssLogShellLineData` record, `EtaIntegralStructureS`, pilot nonzero,
  integral nonempty) as a donor, with the Rss record explicitly marked fixed
  shell, not `Rss`.
- `tmp/sheaf/n8/closure/EtaGuardsActualAttempt.lean` — archive
  `EtaComparisonNonconstantRequirement` and
  `etaComparisonNonconstant_gap`. Also demote `EtaActualFPlaceGuards` to a
  local F-place record: its Theta/Values/reference facts are actual but are
  not a generic guard and must not be used as the global target.
- Any other `Eta*Guard*` file whose fields are arbitrary
  `Rval/Rss/theta/values/reference/region/comparison` plus an existence
  `sorry`.

### Keep

- `tmp/sheaf/n8/closure/EtaIntegralProperActual.lean` — actual compactness /
  noncompactness proof, not a guard.
- `tmp/sheaf/n8/closure/EtaValueGroupLineActual.lean` — actual pilot and
  selected places; keep as donor.
- `tmp/sheaf/n8/closure/EtaIntegralStructureS.lean` — actual integral
  log-shell/volume/Ind data; keep as donor.
- `tmp/sheaf/n8/closure/EtaRssLogShellLine.lean` — keep only as the fixed
  shell record; it must not be called the `Rss` line.
- `tmp/sheaf/n8/closure/P6RelaxedNondegenerateReadout.lean` — keep its actual
  closed/open region and nonzero finite readout as a local donor, not as a
  generic nondegeneracy guard.

## 4. Next executable (no Lean change in this package)

1. Replace the fixed-shell record by an actual varying-region quotient
   `Rss`; prove two distinct classes by two actual regions with different
   volumes.
2. Construct the actual linear isomorphism `eta : Rval -> Rss` (or the two
   independent linear maps `etaQ/etaAnab`) from source data; prove
   `eta 0 = 0`, additivity, bijectivity.
3. Use `pilot != 0` to derive `eta` nonconstant; use equality at the pilot
   plus linearity to derive equality of independent maps.
4. Derive `nu_O(R) != 0` only for actual regions with
   `mu(R) != mu(O)`; do not require it for `R = O`.
5. Rebuild Values as the actual image over varying admissible regions; do not
   store a singleton.
6. Keep all type-level separation/Theta nonzero/reference-region requirements
   out of the target until they are consequences of 1–5.

## Status

- statement_compiles: not applicable (audit only).
- proof_body_checked: not applicable.
- kernel_closed: not applicable.
- target_accepted: no; this retracts unsourced guards and specifies the
  derived route.
- Lean files changed: none.
