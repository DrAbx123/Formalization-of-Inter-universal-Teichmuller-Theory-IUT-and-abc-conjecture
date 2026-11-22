/-!
# stepxi A704 RETRACTED status

History (kept, not deleted):
* `final_conditional_ABC` / `final_theorem_package`: RETRACTED/VACUOUS.
* `natRadicalWeightBound_iff_ABC`: RETRACTED/VACUOUS.
* Reason: `hfull : N = ∏ p_b^e_b` is unsatisfiable for fixed `T`; `N=a+b+c+1`
  scans all odd `N≥5`, so a new prime outside the finite bad set appears.
  Arithmetic support: for every prime `P≥5`,
  `IsABCTriple 1 ((P-3)/2) ((P-1)/2)` and `N=P`.

Retired rows are NOT used as conclusions.

New route (N1, triple-dependent Θ-data):
* bad primes = prime factors of `abc`;
* `q = (abc)^2` (so `v_p(q) = 2 v_p(abc)`);
* normalized weight uses `[F_v:Q_p]/[F:Q]`;
* no `hfull`/N-scaling.

ABC gate: NOT passed. -/
