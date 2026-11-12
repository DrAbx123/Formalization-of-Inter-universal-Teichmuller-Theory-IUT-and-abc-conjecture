# Chain 2 core: model container (A881)

Status: MODEL-level formalization only (explicitly not IUT objects).  `Mzk1Chain2CoreActual.lean`
is green (EXIT=0 + olean=True).  The global Step-(xii) integer range is a parameter.

## Definitions (models, labelled)

- `Chain2Data`: `baseShellVolume` (paper logMuPaper model), `logp > 0` (fixed bad place),
  allowed ord interval `[allowedLower, allowedUpper]` (determined by the global constraint G),
  and `qPilotOrd` with `allowedLower <= qPilotOrd <= allowedUpper` (fields encode G keeping
  the q-pilot member).
- `shellVolume D = baseShellVolume - allowedLower * logp` (additive Haar scaling: the union
  over the interval is the largest shell, attained at the smallest order).
- `ModelRequirementAndBox D req U := req <= shellVolume D ∧ shellVolume D <= U`.

## Proved model theorems

(a) `qPilotRegion_subset_possibleImage` : `allowedLower <= qPilotOrd` (containment of the
    q-pilot region in the possible image, from the data fields);
(b) `model_requirement_and_box` : explicit `req` and upper-box inequalities give the model
    SSIneq-shape;
(c) `qPilotInFamily_holds` : the constraint is not too strong (q-pilot stays in the family);
(d) `middle_case_exists` : explicit numerical witness (`req = 2.5 <= 3 = V <= 4 = U`);
    `chain2_model_ssIneq` : middle case gives `req <= shellVolume` (model SSIneq shape).

## Parameters still undetermined

1. the actual global Step-(xii) integer degree constraint (`allowedLower/Upper`);
2. the multi-place sum over all bad places (the model uses one place; the real volume is a
   sum, shifting the window);
3. archimedean/different/torsion terms (O(1) constants).

## Conclusion

Model-level: middle case exists (conditional SSIneq shape provable).  NOT a proof of SSIneq,
NOT a Lean result about IUT objects.  Next: instantiate `Chain2Data` from the actual
Step-(xii) constraint once its integer range is computed.

## A882 update (stage-4 corrected base)

- New general survival formula (PROVED, `survival_iff`):
  `req <= shellVolume D ↔ allowedLower <= (baseShellVolume - req) / logp` (for `logp > 0`).
  So the survival lower bound on the allowed ord is `allowedLower <= (base - req)/logp`.
- Stage-4 p=11 instance: with corrected `base = 0`, `logp = log 11 = 2.3979`,
  `req = 0.46365`, the bound is `allowedLower <= 0 - 0.46365/2.3979 = -0.1934`;
  stage4's `allowedLower <= -1` (t = -1 or -2) satisfies it.
- New base-zero witness (PROVED, `middle_case_exists_baseZero`):
  `base = 0`, `logp = 2`, `allowedLower = -1`, `allowedUpper = 0`, `qPilotOrd = -1`,
  gives `shellVolume = 2`, `req = 1`, `U = 3`: `1 <= 2 <= 3` (model middle case).
- Row table extended to 10 rows.

## A896 correction (authoritative)

- M2-M4 are **interface placeholders**, not model-level completions. The actual quantitative target is the averaged inequality `(s-1)A <= (1/lstar) sum_j sum_v w_v logVol(hull(P(v,j)))`; per-(v,j) local upper boxes are refuted by ROUTES §6.3 explicit triple `l=11, (1, 13^4-1, 13^4)` (`ord_13(q)=8 > 6.4`).
- Triviality tags: `qPilotRegion_subset_possibleImage` = data field; `chain2_model_ssIneq` = `hmid.1`; `g1_union_eq_single` = `rfl`; `pf_eq_unique_iso`/`scalingUnique` = free Props; `qPilotOrd` does not enter `shellVolume`.
- Real missing theorem: `qPilotRegion subset P => (s-1)A <= VolShell P` (or averaged version). The collapse `exists family/G <-> req <= U` is monotonicity/reindexing, not IUT content.
- G1/G2/G3 are not constraint candidates; see CHAIN2-G-CANDIDATES §5.
