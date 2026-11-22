# C9 mixed profile actuality：rho<=1/2 与 TC-B inclusion

任务：task-314（Prove actual mixed profile rho<=1/2 and TC-B inclusion）。owner：iplsheapt。日期：2026-10-25。短定理/证明或 exact obstruction；不改 Lean/Project/目标；不引入 arbitrary rho；只写本文件。

输入：C9-TAME-LOG-DOMAIN-20261025.md §5/§7（mixed profile 公式与 F_mod=Q section 限制）；C9-TARGET-OTHER-BOUND-20261025.md（task-310 mixed counterexample）；C9-TARGET-GENERATED-20261025.md（task-299）；C9-IND1-GLOBAL-20261025.md（TC-B/full possible-image union）。

## 0. Verdict

**在 C9 target 的 F_mod=Q 条件下，不存在 actual admissible complete C 实现 `0<rho<=1/2` 的 mixed bad/good profile。** TAME §7 自己给出了 exact obstruction：

```
F_mod=Q 时，V→V(F_mod) 是一份 section；每个有理 p 只有一个 selected place；
该 selected place 的 specified bad mass rho 只有 0 或 1。
```

因此 TAME §5 的 mixed-profile local model（任意 0<rho<1）**不是** F_mod=Q 的实际 C 的 possible image。TAME §7 的 `rho<=1/2 ⇒ h_p^aligned>Q_p` 是一个条件局部定理，其 mixed-profile hypothesis 在 F_mod=Q 的 actual C 中不成立。

所以 task-310 的 mixed-profile E_extra 不能作为 source-valid counterexample 来 refute SAT-U；同样，task-314 想用 actual mixed profile 得到 finite P6 的路线被 exact obstruction 阻断。b=273 的 `F>=8821.538` 没有被 mixed profile 否定/修复。

## 1. Why rho is 0 or 1 for F_mod=Q

IUT I Def3.1(e)：`V⊂V(K)` maps bijectively to `V_mod=V(F_mod)`；F_mod=Q 时这是 `V(K)→V(Q)` 的 section。对每个 rational prime p，section 选一个 place `v_p` of K over p。固定 v_p 的 capsule/tensor packet 的 r 个 factors 都在同一个 v_p 上；local reduction type/bad-good status 由 v_p 决定，所有 factors 相同。因此在该 place 的 bad mass

```
rho = (#bad constituents)/(r)
```

只有

```
rho=1  (v_p bad),   or   rho=0  (v_p good).
```

没有 `0<rho<1`。若把不同 rational primes 的 places 混合平均成 rho=1/2，那不是同一个 v_p 的 capsule profile；它改变了 target initial Θ-data/procession，不是原 C 的 possible image。TAME §7 已明确：

```
不能把 K 的所有 conjugate places 改成新的 rho=1/2 平均来回避 uniform 情形。
```

## 2. TAME §7 mixed comparison is conditional

TAME §7 proves: if a mixed profile with `rho<=1/2` existed, then

```
h_p^aligned/logp >= -(b/e)(1/m)Σ j² rho^{j+1} > -rho b/e = Q_p/logp,
```

using `Σ j²rho^{j+1}/m < rho` for rho≤1/2. This is a valid **conditional local inequality**. But TAME also states it has not added rho≤1/2 to the original C hypotheses, and for F_mod=Q the section forces rho∈{0,1}. Thus the inequality cannot be applied to an actual F_mod=Q complete C to get finite P6.

## 3. TC-B inclusion does not rescue a non-actual profile

TC-B says H_C is the hull of the **actual** full possible-image family. A mixed-profile region is included only if it is an actual possible image. For F_mod=Q, the section argument says it is not: at a selected place all factors share the same reduction status. Therefore

```
mixed E_extra ∉ actual U_C  =>  TC-B does not put it in H_C.
```

Task-310's mixed counterexample is a countermodel to a **relaxed local model**, not a source-valid target counterexample under F_mod=Q. No arbitrary rho can be inserted into the target; doing so changes V/V_mod/Θ-data.

## 4. Exact decision

**Theorem 4.1 (mixed-profile exclusion for F_mod=Q).** An admissible complete C with F_mod=Q and Def3.1(e) section V→V_mod cannot have a selected-place capsule with `0<rho<1`. Hence it cannot realize the mixed-profile hypothesis of TAME §7; neither `h_p^aligned>Q_p` nor TC-B inclusion of a mixed region applies. The mixed route to finite P6 is blocked, not by a missing estimate but by the target's section/bad-mass structure.

Consequences:

- No actual mixed rho≤1/2 complete C under F_mod=Q; TAME §7's finite P6 conclusion is not available for the C9 target.
- The task-310 mixed profile is not a source-valid E_extra; SAT-U is not refuted by it in the actual target.
- b=273/uniform rho=1 remains the actual profile; the upper-side issues (SAT-U) are unchanged.
- If one enlarges F_mod or changes V_mod/section, that is a different target/initial Θ-data, not an escape allowed by the no-arbitrary rule.

## 5. Proved / conditional / impossible

Proved exact:

- F_mod=Q + Def3.1(e) section ⇒ per selected rational p, capsule bad mass rho∈{0,1};
- no 0<rho≤1/2 actual mixed profile in this target;
- TAME §7 inequality is conditional on a hypothesis not realized;
- TC-B only includes actual possible images; mixed E_extra is not actual.

Conditional:

- TAME §7 local mixed inequality (if rho mixed were allowed);
- larger F_mod/other V_mod targets (outside C9 target);
- actual complete C/CFTH/TC/arch.

Impossible/obstruction:

- actual F_mod=Q C with 0<rho<1 at a selected place;
- using mixed profile to refute SAT-U or prove finite P6 in the C9 target;
- averaging conjugate places to manufacture rho=1/2.

## 6.5 Correction record（lead scope correction）

Per the scope correction: the TAME §5 mixed bad/good profile is a **different profile**, not a possible image of the fixed `F_mod=Q` uniform target. The I Def3.1(e) V-section forces bad mass `rho∈{0,1}`; C9-GLOBAL §1 explicitly forbids replacing unselected conjugates by `rho=1/2`; task-307 classifies the use of mixed profiles as **E3 profile change**.

Therefore:

```
- mixed-profile results (task-303/304/305/310/311/313) are profile-change/conditional;
- they are NOT usable for original P6;
- no mixed P6 rescue, mixed counterexample, or mixed U refutation is claimed.
```

In particular, the mixed `E_extra`/U_other counterexample written in C9-TARGET-OTHER-BOUND-20261025.md (task-310) is **withdrawn as a P6/SAT-U refutation**: it is a countermodel for a relaxed E3 profile, not a source-valid possible image of the fixed F_mod=Q uniform target. The uniform all-bad `rho=1` profile is the only actual profile under the C9 target; b=273 status is unchanged.

## 6. Conclusion

The actual mixed profile rho≤1/2 **cannot be realized** in an admissible F_mod=Q complete C: the IUT I Def3.1(e) section gives one selected place per rational prime, and at a fixed selected place all capsule factors have the same bad/good status, so rho∈{0,1}. TAME §7's mixed-profile finite inequality is a conditional local theorem whose hypothesis fails for the C9 target. TC-B cannot include a non-actual mixed region. Therefore the mixed-P6 route is blocked by an exact obstruction; the task-310 mixed counterexample is not source-valid under F_mod=Q, and SAT-U/b=273 status is unchanged. No arbitrary rho; no Lean/Project edits; P6 open.

