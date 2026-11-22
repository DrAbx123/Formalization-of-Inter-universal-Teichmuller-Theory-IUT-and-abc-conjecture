/-!
# stepxi final status (A713 update)

## RETRACTED (history retained, not deleted)
* `final_conditional_ABC` / `final_theorem_package`: RETRACTED/VACUOUS;
* `natRadicalWeightBound_iff_ABC`: RETRACTED/VACUOUS;
* reason: `hfull` unsatisfiable for fixed `T`; `N=a+b+c+1` N-scaling is not the paper structure.

## Three-state semantics (unchanged)
PROVED: Cor 3.12 requirement chain (not load-bearing); corrected-region Gap1 full bad support;
corrected Gap2 shape => ABC; Gap2 shape <=> BadSumWeightBound.
NAMED: corrected-region Gap2 shape (only remaining named input).
NOT_PROVED: ABC => Gap2; ABC gate NOT passed.

## New route (N1, triple-dependent Theta-data)
* bad primes = prime factors of `abc`;
* `q = (abc)^2`;
* normalized weight uses `[F_v:Q_p]/[F:Q]`;
* no `hfull`/N-scaling.

## A713 infrastructure facts (recorded from lead)
* sorry/axiom audit over 1,011 files: 0 true hits;
* 7 lana dependency trees vendored to repository root;
* qpilot fetched 12 missing modules (rev 04ab863a);
* lana chain (114 files) queued in watchdog (closure=1367, dirty=850, DAG_MAX=16).

These are status records only; stepxi did not modify other lanes' files. -/
