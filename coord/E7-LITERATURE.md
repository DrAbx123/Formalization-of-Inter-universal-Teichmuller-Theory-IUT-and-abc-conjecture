# E7-LITERATURE — Pasten: what exactly is proved about delta / Szpiro / abc

Status: literature check, 2026-11-12. Read-only. Not Lean evidence. **arXiv original/published status: UNVERIFIED** — arXiv pages were unreachable in this environment; version/date/publication below are second-hand/search-snippet level only.

## 1. Papers

### P2018
- H. Pasten, *Shimura curves and the abc conjecture*.
- arXiv:1705.09251; v1 2017-05-25, v4 2018-07-05 — **UNVERIFIED** (arXiv page unreachable; version/date second-hand only).
- Published version: J. Eur. Math. Soc. (JEMS), best current knowledge — **UNVERIFIED** (publication status not checked against JEMS). arXiv is authoritative only nominally.

### P2026
- H. Pasten, *Improved bounds for Szpiro's conjecture*.
- arXiv:2609.17390v1; submitted 2026-09-15 — **UNVERIFIED** (arXiv page unreachable; version/date second-hand only).
- Preprint; peer-review status **UNVERIFIED** in this session.

## 2. P2026 main theorem (exact)

Notation from the paper:
- E/Q elliptic, Delta = |Delta_min(E)|, N = conductor(E);
- h(E) is the **Faltings height** (not the stable one);
- from [8], log Delta << max(1, h(E));
- an **admissible factorization** N = D M means gcd(D,M)=1, D squarefree, and D has an
  even number of prime factors; phi is Euler's totient.

**Theorem 1.1 (Main result).** For E/Q, an admissible factorization N = D M, and a prime
ell with ell not dividing N:
~~~
h(E) << M * phi(D) * log(ell)
~~~
where the implicit constant is absolute (independent of all previous data) and effective.

Consequences (exact):
- **Corollary 1.2.** All E/Q satisfy h(E) << N log log N. (Makes the earlier
  GRH-conditional estimate unconditional.)
- **Corollary 1.3.** For a fixed finite set S of primes, all E/Q semistable outside S
  satisfy h(E) <<_S N, with effective constant depending only on S.
- With log Delta << max(1,h(E)): log Delta << N log log N for all E/Q, and
  log Delta <<_S N for semistable-outside-S curves.

Not in P2026: no modular degree delta_{N,1}, no product of e_p bound, no Ribet-Takahashi
ratio, no unconditional Szpiro (the bound is far weaker than log Delta << log N), and no
claim of abc. The paper says the methods build on the author's Shimura-curve approach to
abc; it does not deduce abc.

## 3. P2018 results (from the fetched introduction)

Recalled:
- **Conjecture 1.1 (Szpiro).** There is kappa>0 such that all E/Q satisfy
  Delta_E < N_E^kappa.
- **Conjecture 1.2 (abc, Masser-Oesterle).** There is kappa>0 such that all coprime
  positive a,b,c with a+b=c satisfy abc < rad(abc)^kappa.
- Classical Frey construction: for a+b=c, E_{a,b,c}: y^2=x(x-a)(x+b),
  Delta_E=(abc)^2, N_E=rad(abc) up to a bounded power of 2; hence Szpiro for Frey curves
  implies abc. This is a reduction, not a proof of abc.

Main results relevant to E7:
- **Theorem 1.3 (Manin constant; Cor 10.2).** For a fixed finite set S, there is M_S>0
  such that if N is squarefree away from S and f in S_2(N) is a Fourier-normalized Hecke
  newform with rational eigenvalues, then c_f <= M_S.
- **Theorem 1.4 (cokernel of component groups; Thm 6.17).** There is kappa such that for
  squarefree N=DM admissible with M not prime, for q_{D,M}:J_0^D(M)->A_{D,M}, for every
  prime p|D: #coker(Phi_p(J_0^D(M))->Phi_p(A_{D,M})) <= kappa.
- **Ribet-Takahashi ratio (recalled).** delta_{D,M} is the integer such that
  q_{D,M} o q_{D,M}^vee = [delta_{D,M}], and delta_{1,N}=deg(phi:X_0(N)->A). Then
  delta_{1,N}/delta_{D,M} = gamma * prod_{p|D} v_p(Delta_A),
  where gamma in Q is supported at primes ell with A[ell] reducible.
- **Theorem 1.5 (global comparison; Cor 6.2).** Under (i) N squarefree and M not prime,
  or (ii) A isogenous to a Frey-Hellegouard curve and M divisible by at least two odd
  primes:
  log(prod_{p|D} v_p(Delta_A)) = log delta_{1,N} - log delta_{D,M}
    + O(log D / log log D),
  absolute implicit constant. (Thm 6.1 allows additive reduction at a fixed finite set.)

Not in P2018:
- no unconditional bound log delta_{1,N} <= (2+eps) log N + C for general N;
- no unconditional Szpiro or abc theorem;
- height/delta applications are conditional or restricted (semistable/Frey; additive
  reduction only outside a fixed finite set).

New vs known (paper's own accounting, as far as fetched):
- New: uniform Manin-constant bound in additive reduction (Thm 1.3), component-group
  cokernel bounds (Thm 1.4), global comparison Thm 1.5 with explicit error.
- Known/imported: modularity, Jacquet-Langlands, Ribet-Takahashi, Mazur's semistable
  Manin constant, Abbes-Ullmo-Raynaud and Cesnavicius inputs, Darmon-Granville generalized
  Fermat equations, Arakelov/Colmez tools.
- Exact numbering of the main Faltings-height theorems of P2018 is not fully captured in
  the fetched 100k-character preview; abstract claims improved effective bounds for
  Faltings height in terms of conductor. Marked **PENDING exact numbering**.

## 4. E7 verdict

- P2026 is an arXiv theorem (not our green Lean theorem): h(E) << N log log N and,
  for semistable outside fixed S, h(E) <<_S N. Genuine Szpiro-direction progress, but far
  from Szpiro log Delta << log N, and it does not prove abc.
- P2018 is a research framework with partial unconditional results (Manin constant,
  component groups, delta comparison), not a general delta bound and not abc.
- Therefore E7 is **research frontier**, not an already-published complete theorem that
  can be dropped into our route as a finished delta bound. The usable published input for
  a conditional bridge is the Ribet-Takahashi comparison (P2018 Thm 1.5) plus P2026's
  height bounds; both still require a real delta upper bound or an independent argument to
  reach Szpiro6Shape.

No Lean claims, no port, no fake axioms.

## 7. Lean formalization (A860, `Mzk1E7GapStatementActual.lean`, EXIT=0, olean=True)

* `E7Scale` (`logN`, `logDelta`, `logModDegree`);
* `PastenThm76 ε C D := D.logDelta ≤ (6+ε)·D.logModDegree + C`;
* `DeltaDegreeBound C' := ∀ D, D.logModDegree ≤ D.logN + C'`;
* **`E7GapStatement : Prop := ∃ C', DeltaDegreeBound C'`** — the true missing input;
* `E7AcceptDeltaBound := E7GapStatement`, `E7RejectDeltaBound := ¬ E7GapStatement`;
* proved: `szpiro_of_pasten_and_delta` (`(6+ε)` form), `szpiro6_of_pasten_and_delta`
  (`ε=0`, `logΔ ≤ 6 logN + C''`), `e7_accept_reduction`;
* no δ bound is assumed or proved: the file only records the conditional reduction.

Cross-route note: the IUT/Step-XI route's own gap is the choice-existence lemma
`StepXIAdditionalLemma A V κs := ∃ κ∈κs, -A-κ ≤ V` (equivalent to SSIneq; see
`Mzk1StepXIFormalizationAttemptActual` and `Mzk1StepXIChoiceActual`).  E7 and Step XI
share only the final `Szpiro6Shape`/`SSIneq` targets; neither supplies the other's gap.
