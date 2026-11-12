# FEAS-MOTIVIC — p-adic integration / motivic transfer feasibility

Status: feasibility analysis; no compile. External references:
- Denef–Loeser, p-adic integration and motivic integration (resolution-based formula);
- Ax–Kochen / Ershov transfer principles for local fields.

## 1. What the tools say

Denef–Loeser: a p-adic integral of a constructible function over a definable set can be computed by resolution of singularities. In the monomial/valuation-ball case it reduces to geometric series, e.g. for a ball {x : ord_p(x) >= n} in Q_p^d the Haar volume is p^(-nd) (up to normalization), and integrals of |f|^s are rational functions in p^(-s).

Ax–Kochen/Ershov: first-order statements in the language of valued fields transfer between Q_p and F_p((t)) for residue characteristic large (or between all sufficiently large p). This transfers definable set identities and residue-field counts, not real log-volumes directly.

## 2. Is our log-shell volume a p-adic integral?

Yes locally: componentVol is a normalized Haar integral over a lattice/set in a finite-dimensional Q_p-vector space; logShell is defined by valuation/norm inequalities, hence is a p-adic definable (semi-algebraic/valuation-definable) set. The tame formulas

  integral over {ord >= n} = p^(-n d)

and the geometric-series computations are exactly the elementary p-adic integration behind componentVol.

But the global q/theta volume also contains:
- real logarithms log p and log q;
- archimedean factors (real theta values, archDefect);
- arbitrary qOrder and weights;
- hull enlargement by indAut.
These are not first-order valued-field data.

## 3. Can motivic/transfer reduce the inequality to a decidable polynomial/combinatorial identity?

Only after:
1. expressing every region as a definable set in the valued-field language;
2. expressing the volume as a constructible motivic function/integral;
3. proving the transfer of the resulting identity to Q_p;
4. handling log p and archimedean terms outside the valued-field language.

Step 1 is local and plausible for log-shell/tame regions (valuation balls, monomial ideals). Step 2 needs the Denef–Loeser formalism (resolution of singularities, Grothendieck ring, constructible functions), absent from Mathlib/LeanFormal. Step 3 needs Ax–Kochen/Ershov transfer for integrals, also absent. Step 4 is a real obstacle: log p and log q are not definable in the valued-field language; one could compare exponent vectors before taking logs, but the archimedean and real q data remain outside.

For the local valuation-ball part, the computation is already available through Haar measure and geometric series; no motivic machinery is needed. For the global inequality, motivic integration would at best produce a finite combinatorial expression, not automatically the real inequality.

## 4. Judgment A/B/C

A — feasible now:
- local Haar/valuation-ball integrals, componentVol_mono, logShell_eq_integer, tame shell formulas;
- the existing componentVol/logShellRadius computations.
Not the global inequality.

B — conditionally feasible with new definitions:
- define a restricted class of valuation-definable/monomial regions and prove their p-adic integral by geometric series;
- derive logShellRadius/tame formulas for those regions;
- state the q/theta comparison as a hypothesis.
This is a local computation layer, not a reduction of the target.

C — not feasible now:
- full Denef–Loeser constructible motivic functions, resolution of singularities, motivic measure, Ax–Kochen/Ershov transfer for integrals, and a treatment of log p/archimedean data;
- even then the real log q/Theta and archimedean terms are outside the first-order theory.

Verdict: C for the global motivic/transfer route; B only for a local monomial/valuation-ball computation; A does not reach the target.

## 5. Minimal formalization if B is attempted

1. Valued-field definable sets (valuation balls, monomial conditions).
2. p-adic Haar measure on Q_p^d and the geometric-series integral:
   volume({x : min_i ord(x_i) >= n}) = p^(-n d).
3. Integrals of monomials |x|^s over valuation balls, as rational functions in p^(-s) (or directly for s=1).
4. A restricted Denef–Loeser formula only for monomial/regular regions (no resolution).
5. Derive local logShellRadius/tame formulas from 2-4.

What is missing for the target:
- identification of q/theta regions with such definable sets;
- real log p/q and archimedean factors;
- transfer principle for integrals (Ershov/Ax–Kochen).

## 6. Recommendation

- Use p-adic integration only as a sanity/normalization tool for local log-shell volumes; the existing componentVol and Haar lemmas already encode it.
- Do not expect motivic integration to decide the q/theta inequality: the real logarithms, archimedean factors, and source-specific region identification are outside its scope.
- Keep the current route: Form C arithmetic (green), theta subset q/volume identities (GAP), local log-shell computations (green where available).
- External literature: Denef–Loeser p-adic/motivic integration; Ax–Kochen/Ershov transfer; neither is in the current Lean tree.
