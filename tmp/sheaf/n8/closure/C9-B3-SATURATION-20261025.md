# C9 b=3 saturation upper and the P6/counterexample split

Task: task-293 (C9-B3-SATURATION-20261025). Owner: logdescent. Date: 2026-10-25. Short theorem/proof-or-obstruction; only this file written; no Lean/Project/target/other-owner edits; no arbitrary. P6 unproved; target_accepted=false.

Inputs: C9-P6-NOGO (task-256); C9-TC-EQUALITY (task-266); C9-TARGET-POSITIVE/EXTRA (tasks 271/285); C9-BI-REGION (274); C9-ARCH-HULL; E47 convention.

Convention E47: F(C)=Q_C-h_C; P6 is h_C>=Q_C, equivalently F<=0. F>0 is a P6 counterexample. B_I-zero normalization; A_proc=11.5log pi=13.164393687...

## 0. Verdict

For b=3, a saturation upper

    (U3)  h_C <= max(H_A,H_B)+h_inf = H_B+h_inf                        (0.1)

would produce an exact h_inf-dependent split:

- h_inf < -S_3 := -(12/41)log p = -2.7563226845...
      -> h_C <= H_B+h_inf < Q_p, so h_C<Q_p and P6 FAILS; this is a counterexample, independent of the B=O_K/B=I branch.
- h_inf = -S_3
      -> h_C<=Q_p; P6 holds iff h_C=Q_p; strict inequality gives a counterexample. Upper alone does not decide.
- h_inf > -S_3
      -> upper alone does not decide (it allows both h_C<Q_p and h_C>=Q_p);
         if the target B=I sibling region is present (task-274), the lower bound h_C>=H_B+h_inf>Q_p proves P6; without that lower bound, P6 is undetermined.

For b=273 the same saturation upper would **repair the b=273 no-go** conditionally:

    h_C <= H_B+ h_inf <= H_B+A_proc = -8884.245232030... < Q_p=-62.706341073...,
    so F=Q_C-h_C >= 8821.538890956... >0.

Thus, under U273, b=273 is a P6 counterexample in both B branches with margin at least 8821.54. Without this upper, C1 (which is a lower bound h_C>=H_A+h_inf) does NOT prove F>0; it only gives F<=Q-H_A-h_inf. The b=273 no-go therefore needs a saturation upper/maximality theorem (or an equality h_C=H_A+h_inf), not merely C1/CFTH/TC. This is the exact logical repair/refutation point.

The saturation upper is not proved by the source: TC-B/TC-C give containment and volume preservation, not exhaustion. It remains a conditional theorem; no arbitrary target region is assumed.

## 1. The saturation upper and its exact content

For b=3 the local branch values are

    H_A=(-411/41)log p=-94.4040519457...,
    H_B=(9/41)log p=2.0672420134...,
    Q_p=(-3/41)log p=-0.6890806711...,
    S_3=(12/41)log p=2.7563226845...,
    H_B+H_A difference =420/41 logp=96.471293959... .                  (1.1)

The saturation upper U3 says the target hull is exhausted by the two local branches plus the arch component:

    h_C <= max(H_A,H_B)+h_inf = H_B+h_inf.                            (1.2)

Equivalently, there is no extra target possible-image region beyond the union of the B=O_K and B=I branch hulls. This is exactly the missing reverse-inclusion/maximality direction (C9-TC-EQUALITY EQ1); TC-B alone gives H_C larger, not smaller.

Conditional on U3:
- the upper is branch-independent (max is H_B);
- the difference H_B-Q_p=S_3 is positive;
- the threshold h_inf=-S_3 is exact.

## 2. b=3 split theorem

Theorem 2.1 (conditional on U3). Let C satisfy C1/CFTH/TC/arch and the b=3 uniform profile with saturation upper (1.2). Then:

(i) If h_inf < -S_3, then h_C <= H_B+h_inf < Q_p, so F>0; P6 fails with margin at least -S_3-h_inf. This holds for both selected B branches.

(ii) If h_inf = -S_3, then h_C<=Q_p. P6 holds iff h_C=Q_p; if h_C<Q_p, F>0 and P6 fails. The upper alone gives no strict decision.

(iii) If h_inf > -S_3, then h_C<=H_B+h_inf, but H_B+h_inf>Q_p; the upper does not force F>0 or F<0. Additional lower data are needed:
    - if the target contains the B=I sibling region (task-274), h_C>=H_B+h_inf>Q_p, so P6 holds;
    - if only the selected B=O_K lower bound is available, h_C>=H_A+h_inf<Q_p (because h_inf<=A_proc<D_3), so P6 is undetermined by C1+U3; an extra target region of volume at least Q_p-(H_A+h_inf) would be needed.

Proof. Insert max=H_B and compare to Q_p; the lower/upper directions are as stated. The B=I lower bound is task-274; the B=O_K C1 lower is H_A+h_inf. QED.

Numerical illustration:
- h_inf=A_proc: H_B+h_inf=15.2316357007>Q_p; upper allows P6; with B=I lower, exact h_C=15.2316 and P6 holds.
- h_inf=0: H_B=2.0672420134>Q_p; upper allows P6; without B=I lower, undetermined.
- h_inf=-3<-S_3: H_B-3=-0.9327579866<Q_p; P6 fails (counterexample) regardless of branch.

## 3. B=O_K versus B=I comparison

Under U3, the two branches share the same upper H_B+h_inf; the upper is governed by the larger B=I local value, not by the selected B=O_K value.

- h_inf < -S_3: both branches are counterexamples; B choice is irrelevant.
- h_inf > -S_3:
    * If the actual selected branch is B=I, the lower h_C>=H_B+h_inf>Q_p proves P6 without needing the selected B=O_K C1 lower.
    * If the selected branch is B=O_K, C1 gives only h_C>=H_A+h_inf, which is <Q_p for h_inf<=A_proc (since H_A+A_proc< Q_p); P6 needs the target to include the B=I sibling region (task-274). If it does, U3 and the B=I lower pin h_C=H_B+h_inf, and P6 holds. If it does not, U3 leaves P6 undetermined; a counterexample is possible but not forced.
- At h_inf=-S_3, equality h_C=Q_p is the only P6 case; otherwise counterexample.

Thus U3 makes B=I the favorable/dominant target branch; B=O_K alone is insufficient. This aligns with task-271/274: the B=I sibling supplies the +96.47 surplus over the B=O_K hull.

## 4. b=273: repair/refutation of the no-go upper side

For b=273:
    H_A=(-39156/41)logp=-8993.880919676...,
    H_B=(-38736/41)logp=-8897.409625717...,
    Q_p=(-273/41)logp=-62.7063410734...,
    A_proc=13.164393687... .                                          (4.1)

Saturation upper U273 would give
    h_C <= H_B+h_inf <= H_B+A_proc
        = -8884.245232030... < Q_p,
so
    F=Q_p-h_C >= 8821.538890956... >0.                               (4.2)

Thus U273 would make b=273 a P6 counterexample in both B=O_K/B=I branches, with margin at least 8821.54; this repairs the upper side of the task-256 no-go and makes it branch-independent.

Without U273, C1 only gives
    h_C >= H_A+h_inf,
hence
    F = Q_p-h_C <= Q_p-H_A-h_inf = D_273-h_inf,                      (4.3)
which is an **upper** bound on F, not a lower bound. It is compatible with F<=0 (P6) if the target hull contains an extra region. In particular, C1 + CFTH + TC + arch alone do not prove F>0; the task-256 argument uses the saturation/equality direction (local hull upper) and is therefore conditional on U273, not only on C1. This is the exact repair/refutation point:

- U273 true and a complete C exists -> b=273 P6 false (counterexample) with margin 8821.54.
- U273 false (extra target region) -> C1 does not refute P6; the b=273 no-go is not established. Task-285 shows no source-constructed extra region beyond B=I, but does not prove U273; the missing object is the saturation upper itself.

## 5. Exact obstruction to U3/U273

TC-B says H_C is the hull of the full possible-image family, which gives a **lower** inclusion; it does not give an upper. TC-C volume preservation is an isometry, not an exhaustion/maximality statement. C1 is a lower bound. The C9-TC-EQUALITY countermodel (add an extra possible-image region epsilon>0 while preserving all TC containment/preservation semantics) satisfies TC-B/TC-C but violates U3 by epsilon. Hence U3 is not a consequence of TC-A..H/TC-S; it is an independent saturation/maximality theorem (EQ1) that is missing.

Task-285's source-conditional saturation result (TAME §6 only B=O_K/B=I local lattices) supports U3 within the saturated source model, but it does not prove the target reverse inclusion for the full Ind1/gluing/BPS/Theta possible-image family. Under the source-conditional model U3 is a theorem; under the actual target it remains a conditional hypothesis. No arbitrary enlargement is used: U3 is stated as an explicit hypothesis and its failure is the exact obstruction.

## 6. Proved / conditional / missing

Proved conditional on U3:
- b=3 split theorem 2.1; threshold h_inf=-S_3; counterexample for h_inf<-S_3; P6 via B=I lower for h_inf>-S_3; boundary equality.
- b=273: U273 -> F>=8821.538890956...>0, counterexample both branches; no P6.
- B=O_K/B=I comparison: B=I dominates under U3; B=O_K needs target B=I region.

Proved without U3:
- C1 only gives lower h_C; consequently F<=D-h_inf, no counterexample forced. The tasks-256 b=273 no-go needs U273 (or equality), not C1 alone.
- Task-274 B=I region: conditional h_C>=H_B+h_inf and b=3 P6 iff h_inf>=-S_3.
- Task-285: no source-constructed new region beyond B=I; exact obstruction, but not an upper theorem.

Missing:
- U3/U273 saturation upper/maximality (EQ1) for the actual target;
- actual B=I realization/Theta/TC;
- actual h_inf and complete C.

## 7. Conclusion

The saturation upper is the decisive missing piece. If h_C<=H_B+h_inf holds for b=3, the P6/counterexample split is exactly:
    h_inf<-S_3 -> counterexample;
    h_inf=-S_3 -> P6 only at equality;
    h_inf>-S_3 -> P6 if B=I target region is present, otherwise undetermined.
For b=273, the same upper would repair the no-go conditionally and make P6 false with margin >=8821.54. Without the upper, C1 alone does not prove the b=273 counterexample; the b=273 no-go is conditional on saturation/maximality, not on C1/CFTH/TC/arch alone. The upper is not proved by TC; it is the exact obstruction. No arbitrary target region is assumed.

Only C9-B3-SATURATION-20261025.md written. No Lean/Project edits. target_accepted=false; P6 conditional on saturation upper, otherwise open.
