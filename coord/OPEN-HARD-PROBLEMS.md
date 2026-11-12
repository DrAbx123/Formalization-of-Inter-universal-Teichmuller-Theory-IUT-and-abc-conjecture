# OPEN HARD PROBLEMS (for external review) — 2026-11-10 22:50

Repo: D:\lean, Lean 4 + Mathlib pinned v4.32.2. All formalization assets below are green/CITABLE unless marked named.
Context: IUT 3.12 prerequisite formalization; gate table V150@12275/FEE21161 (GATE NOT PASSED); rational F=Q component closed; 6 named class-B inputs remain. binding HOLD.

## Problem A — beta-avoiding rational Belyi (the central remaining math gap)
Statement: for every finite S subset of Q and beta in Q with beta notin S, construct q in Q[X] with
  (1) 0 < q.natDegree; (2) forall s in S, q.eval s in {0,1}; (3) q.eval beta notin {0,1};
  (4) forall z : C, aeval z (derivative q) = 0 -> aeval z q = 0 or 1  (CV(q) subset {0,1}).
Status: true and formally PROVED for |S| <= 3 (files Mzk1BetaAvoidingBelyiSmallActual + Mzk1BetaAvoidingExteriorActual;
  belyiBetaAvoidingSmallStatement_proved). General |S| >= 4 is NAMED (BetaAvoidingBelyiBaseInput).
KNOWN OBSTRUCTIONS (kernel-checked):
- the canonical TauCeti degree-reduction step f = B_{m,n} o (affine min->0, max->1, third c -> r=m/(m+n))
  FAILS for S={0,1,3}, beta=4: for EVERY admissible (m,n), f(4) = f(1) = 1 (tauCetiStep_not_betaAvoiding).
- outer Belyi composition cannot repair f(beta) in {0,1} because every Belyi R satisfies R(1)=0.
- the scaling family (m,n)=k(p,q) satisfies B_{kp,kq}(u) = (B_{p,q}(u))^k exactly
  (belyiConst_scaling/belyiEvalQ_scaling); bad sets are all-k (=1), even-k (=-1), or {0};
  counterexamples: p=q=1,u=1/2 (all k bad), and collision B_{1,1}(1/4)=B_{1,1}(3/4).
- target IS satisfiable for the obstruction instance: q = B_{1,1} o B_{2,1}, q(0)=q(3)=0, q(1)=1, q(4)=6400.
CURRENT ATTEMPT: choose third point c (or pair/orientation) so B_{p,q}(u) != 1 (u = affine image of beta), then odd k;
  residual lemma: exists_third_point_avoiding_one (under active one-off). For |S| >= 4 exterior beta this may need
  multi-step/non-canonical construction; no proof yet.
What would solve it: a general construction (multi-step Belyi recursion with beta tracking, or different inner Belyi B'
  with two-layer outer R as in the |S|=3 exterior proof), or a counterexample for some (S,beta).

## Problem B — paper Lemma 2.3 (normalization/separation with rational coefficients)
Paper (Noncritical Belyi Maps, around lines 120-143): for finite S subset of P1(Qbar) and beta outside S,
  there is lambda in P1(Q) such that f(x)=1/(x-lambda) satisfies f(beta) != 0,inf; f(alpha) != inf for alpha in S;
  and |f(beta)| >= C * |f(alpha)| for all alpha in S, some C>0. Used (lines 163-184) to normalize |alpha|<=1 and |beta| large
  by an automorphism with RATIONAL coefficients before the minpoly step.
Status: not formalized. Assets: Mzk1MoebiusP1Actual / Mzk1MoebiusP1CActual / Mzk1MoebiusP1QbarActual (MoebiusData/AC,
  mapPoints, comp, nonconstant, derivativeNumerator_ne_zero, CV empty, mapsTo_specialSet iff).
Hard points: archimedean size estimates; rational choice of lambda (finite distance argument); Qbar->Q coefficient requirement.

## Problem C — algebraic nested (m,d) induction, paper lines 163-206
Goal: formalize the paper's reduction of Lemma 2.4 to the rational case:
- S finite subset of P1(Qbar), beta notin S; may replace S by Galois-stable set;
- m(S) = max reduced degree [F:Q]-1 of fields of definition of points; d(S) = sum of reduced degrees of points attaining m(S);
- nested induction on (m(S), d(S)): for m,d != 0 pick alpha0 in S with [Q(alpha0):Q]=m(S)+1;
  normalize by Lemma 2.3 automorphism + positive rational scaling so |alpha|<=1 (alpha in S), |beta| large;
  f0 = monic minpoly of alpha0; verify f0(beta) notin S' = f0(S) union f0(roots of f0');
  for alpha' in f0(roots f0'), [Q(alpha'):Q] < d0 (since f0, f0' in Q[x], deg f0' <= d0-1); deduce either m(S')<m(S) or m(S')=m(S) and d(S')<d(S);
  recurse and compose. Also the field-of-definition/infinite-fixed-field descent (finite Galois descent PROVED; infinite component class-B).
Status: NAMED (AlgebraicNestedInductionInput is definitionally the paper-scope target verdict: Iff.rfl in Mzk1LayerAConsumerActual).
Already PROVED and reusable: s3135_criticalPoint_degree_drop, valueDegreeDrop_proved/fieldDegreeDrop_proved,
  s3135_mOfPoints_lt_of_forall_reducedDegree_lt, s3135_f0S0_m_lt, CV composition law, measure monotonicity, descent finite-Galois.
Hard points: field-of-definition degrees over Qbar, Galois-stable sets, minpoly tower, reduced-degree bookkeeping, infinite fixed field.

## Problem D — H6 GeometricCore line-bundle isomorphism
Precise witness (Mzk1GeometricCorePreciseActual) replaces three free Prop fields by: MapsTToZero, UnramifiedOverZero
  (LevelSetsGenericallyEtale from ported flt_th finite-map data), PullbackIsoDegree (m = |D|). toOld conversion
  now proved (Mzk1GeomCorePreciseToOldActual). The named class-B piece left: existence of the precise witness, in particular
  the full line-bundle isomorphism psi^* O(1) ~= O(D) (only the degree identity is proved).
Hard points: scheme-level finite morphism/Cartier divisor/line bundle API in pinned Mathlib; level-set etaleness construction.

## Problem E — deep IUT inputs (L7/L8) — likely out of scope, listed for completeness
AbsTopIII05, H5 O^x stabilization, H7/Ob9 arbitrary iterate, EtTh realization deeper rows, IUT IV section 1 inputs (uniform height-vs-volume);
all currently named class-B. Full formalization would require substantial anabelian/log-geometric theory not in Mathlib/TauCeti.

## What is NOT hard / already closed (do not duplicate)
- rational 2.2 gate unconditional F=Q: RationalGate (baseProvider_holds via BaseGood and via one-off #11; step provider PROVED; target_rational PROVED).
- rational 2.4 CV accounting: criticalValuesOverC_eq, CVCompositionLawStatement, SpecialSetPreservationStatement, CVCompat PROVED.
- two kernel-checked spec repairs: literal 0/1 CV target for unnormalized gPoly REFUTED (counterexample; image-based invariant PROVED;
  normalized belyiNormGPoly 0/1 PROVED); badParamSet_finite/exists_good_param REFUTED (scaling identity; corrected sharp theorems PROVED).
- 2.4 conditional base/assembly, consumer design + F=Q real consumer (rational 2.2 o 2.3), consumer24 adapter + wiring (rfl slots).
- S6 |S|<=3 beta-avoiding fully proved (incl. exterior; belyiBetaAvoidingSmallStatement_proved).
