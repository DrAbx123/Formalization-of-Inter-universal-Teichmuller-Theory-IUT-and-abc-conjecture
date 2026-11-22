# C9 new-math：TC target container 的几何/stack-theoretic 构造

任务：task-241（new geometric proof of TC target container）。owner：iplsheapt。日期：2026-10-25。自然语言 stage1 探索；不改 Lean/Project/目标；不引入 arbitrary containment/volume equality；只写本文件。

背景：TAME (11)-(14) 已撤回；TC-A..TC-H/TC-S 缺失。输入：C9-IND1-GLOBAL-20261025.md；C9-ARCH-GLOBAL-20261025.md；C9-GLOBAL-ASSEMBLY-CORRECTED-20261025.md；C9-CONSTRUCT-KCK/C9-EJ-COMPLETION（C_K/C_F/V/ε 的 source-level 构造）；IUT I Def3.1/4.10；IUT III Def1.1/Prop1.2/Thm3.11/Cor3.12；task-147/149 纠偏。

状态：没有 Lean/Project/kernel/comparator/独立审查；P6 open；target_accepted=false。

## 0. Verdict

**没有得到无条件的 TC 证明。** 本文件得到的是一个 new geometric conditional theorem（TC-G），它把目标容器问题从“环同构 F 是否碰巧把 hull 送进固定 H_C”改写为三个可审计的几何条件：

```
G0  target is the hull of a full versal possible-image family (stacky saturation);
G1  F is induced by an isomorphism of C_K/C_F/V/ε data preserving log-shell/integral/measure;
G2  F is a Q_p-linear/affinoid isomorphism and Hull(F(L)) = F(Hull(L));
G3  normalized log-volume satisfies nu_target = c·F_*nu_source with explicit c>0.
```

若 G0-G3 + TC-A/D/E/F/H 成立，则

```
F(Hull(L)) ⊆ H_C   and   nu(H_C) ≥ c·nu_source(Hull(L)).
```

若 G0 或 G3 不成立，则 **不能**从现有 C_K/C_F/V/ε + theta-pilot 数据推出 target containment 或 volume matching；这不是攻击，而是精确的 no-go 归因。TC-A..H/TC-S 仍不能由本文件闭合。

## 1. 几何对象

固定一份 initial Θ-data 和完整 C 的 source-level 数据

```
C = (F/F, X_F, l, C_K, V, V_bad, ε),
C_K type (1,l-tors)^pm,  C_F×_F K = K-core(C_K),
X_K=E_K\{O};  V a section of V(K)→V_mod;  ε the canonical cusp.
```

令 `S` 是 Θ-pilot/Theta 的允许积分输入，`A(S)` 是 Gaussian/evaluation 作用下的实际区域，`T` 是固定末端 transport，`H_C` 是 IUT III Cor3.12 的 holomorphic hull of the union of possible target images。固定 initial Θ-data、row j、v_Q、Theta-gluing、target column 和 normalization；不扩大 H_C。

不同 realization 之间用 C-data isomorphism 连接：保持 C_K、C_F、V、V_bad、ε、log-shell、mono-analytic integral structure、Kummer labels 和末端 gluing。TC-S 的 corrected symplectic donor 只作为 β 的一种来源；不把 rho 当 homomorphism，不使用 withdrawn boundary-word construction。

## 2. 新的 stack/versal family 构造

定义 groupoid-valued functor `M_C`：objects 是上述完整 C 数据（含 fixed initial Θ-data 和 source/target registration），morphisms 是保持全部上述结构的 C-data isomorphisms。对每个 object 及固定 q/BPS/gluing data，令 `U_C` 为 Θ-pilot possible-image family，

```
U_C ⊂ target packet;   H_C := Hull(U_C).
```

这不是把 H_C 换成更大集合；它是把 Cor3.12 的“union of possible images 的 hull”组织成 versal family。需要一个 source theorem：

```
G0 (versal saturation):  U_C is the full possible-image family for the
    full source Ind1/Ind2/Ind3 orbit, not one fixed representative or one
    fixed component; source and target lie in the same connected M_C-fiber.
```

若 G0 成立，target 的 defining family 在 C-data isomorphisms 下稳定；这是 TC-B 的几何版本。若 target 只是 fixed component `H_{C,j,vQ}`，G0 失败，F 的像可以落在该 component 外；见 §5。

## 3. TC-G：包含与体积的条件定理

令 `L = Hull(⋃_γ γ_+(A(S)))` 是 source hull，F 是 fixed T 下的 packet transport。假设：

```
G1: F is induced by a C-data isomorphism in M_C (not just a field-copy
    or an arbitrary Q_p-algebra isomorphism); it preserves C_K/C_F/V/ε,
    log-shell, integral structure, row/place/gluing and Ind1/2/3 class;
G2: F is Q_p-linear/affinoid, and the chosen Hull is the Q_p-convex/
    holomorphic hull on the same polydisc coordinates, so
    F(Hull(L)) = Hull(F(L));
G3: nu_target = c·F_*nu_source for an explicit c>0 (c=1 if the source
    and target use the same log-volume normalization and tensor degree).
```

**Theorem TC-G (conditional).** 若 G0-G3 与 TC-A/D/E/F/H 的对应结构保持成立，则

```
F(L) ⊂ U_C ⊂ H_C  ⇒  F(Hull(L)) = Hull(F(L)) ⊂ H_C;                (TC-G1)
nu(H_C) ≥ nu(F(L)) = c·nu_source(L).                              (TC-G2)
```

证明：G0 给 `F(L)` 的每个 target 点属于 defining possible-image family `U_C`；`H_C=Hull(U_C)` 包含它，且 hull 对包含单调。G2 给 `F(Hull(L))=Hull(F(L))`，故包含。G3 给体积 pushforward；单调性给 `nu(H_C)≥nu(F(L))`。没有使用任意 H_C 放大，也没有使用 ring iso 自动 measure-preserving。

对 C9 的 target lower bound，若 `ν_source(L)` 是已知的局部/tensor 体积，则 TC-G2 变成显式不等式

```
nu(H_C) ≥ c·nu_source(L);      c 由 normalization/tensor degree 给出。
```

若 c=1，则 volume matching 只需 package 的局部/tensor 计算；若 c≠1，必须把 c 的每个因子（degree、tensor power、archimedean、B_I vs shell-pi normalization）算出，不能设 c=1。

## 4. C_K/C_F/V/ε 在证明中的实际作用

C_K/C_F/V/ε 不是装饰；它们提供三件几何数据：

1. **可迁移的 log-shell/integral structure**：C_K 的 (1,l-tors) orbicurve、C_F 的 K-core、V 的 bad section 和 ε cusp 给出一致的 local log-shell/measure 接口。G1 用它们定义“C-data isomorphism”，排除 arbitrary field-copy。
2. **target family 的 labeling**：V/V_bad 与 ε 决定 bad/row/cusp 的 registration；TC-D/E/H 的 row/place/gluing/Ism 条件可表述为这些 label 的保持。
3. **canonical measure candidate**：若 log-volume 由 C_K 的 log-shell 和 ε cusp 的 normalized measure 决定，则 C-data isomorphism 应送源 measure 到 target measure；这是 G3 的几何来源。**但当前 source 没有证明这个 measure 的 canonicality/normalization 与 IV B_I/shell-pi convention 一致**；所以 G3 仍是条件。

## 5. 什么时候不可能：fixed target component / non-isometric F

### 5.1 Fixed component 反例

若 target 不是 G0 的 full versal hull，而是一个固定 component `H_{C,j,vQ}`（或只含一个固定 representative 的 hull），取 F 的像 `F(L)` 含有一点不在该 component 内；则

```
F(L) ⊄ H_C,   hence F(Hull(L)) ⊄ H_C.
```

这与 F 是 ring isomorphism 无关；ring isomorphism 不能强迫像落入一个未饱和的固定 component。因此：**从当前只固定 component 的 target 数据推出 TC-B 是不可能的**；必须 G0 或额外的 target saturation theorem。

### 5.2 Ring isomorphism 不给体积

一个 Q_p-algebra isomorphism F 可以有任意 determinant/scaling 在 measure 上；即使 F 是线性的，`nu(F(E))` 也不必等于 `nu(E)`。所以

```
TC-B (inclusion)  ⇏  TC-C (normalized-volume comparison)
```

必须 G3 的 explicit c，或独立证明 F measure-preserving。TAME 的 ring-iso 步骤不能替代这个 measure 条件。

### 5.3 当前数据不足

IUT III Cor3.12 只定义 possible images 的 hull，不提供本文件所需的 versal family over `M_C`、source/target connectedness、或 target component saturation。C9-IND1 §5.3 已把 Route A/Route B 列为未证；本文件没有新的 source theorem 来补 G0。C_K/C_F/V/ε 在 task-198/206 也仍是 source-level/conditional，不是 actual complete C。因此：

```
Unconditional TC from current data: IMPOSSIBLE (no G0/G3 theorem).
Conditional TC-G: VALID as an abstract reduction.
```

## 6. Reduction table

| TC condition | TC-G reduction | status |
|---|---|---|
| TC-A source procession | G1 includes C-data iso; β∈Ind1 | conditional |
| TC-B target saturation | G0 full versal family; Hull monotone | conditional; fixed component fails |
| TC-C volume | G3 explicit c and measure descent | conditional; c not computed |
| TC-D row/place | G1 preserves row/vQ/profile | conditional |
| TC-E Theta/gluing | G1 preserves Θ/gluing/q-BPS | conditional |
| TC-F log/Ind3 | G1 lies on allowed log branch | conditional |
| TC-G n/infinity | separate n and +∞; not covered by finite G0 | missing |
| TC-H Ism/Ind2 | G1/G3 track Ism scalar | conditional |
| TC-S donor | corrected H=Φ^{-1}(Sp), not used automatically | conditional/inferred |

## 7. 显式剩余 inequality（可直接作为下一步 lemma）

为了把 TC-G 变为可用，只需证以下两条：

```
(SAT)  U_C is the full Ind1/2/3 possible-image family, and for every
       source γ, T(βγ)(A(S)) ∈ U_C (same row/place/Θ/gluing);
(MEAS) nu_target(F(E)) = c·nu_source(E) for the actual E=Hull(L),
       with explicit c from tensor degree and normalization.
```

若 SAT 成立而 MEAS 只给 c，则 target lower bound 是 `nu(H_C) ≥ c·nu_source(L)`；不能把 c 吸收进任意 normalization。若 SAT 不成立，TC-G 不适用；不能靠扩大 H_C 修补，除非 source 明确允许该 enlargement。

## 8. 结论与下一步

本文件的新贡献不是宣称 TC 已证，而是给出一个**几何/stack-theoretic reduction**：target containment 应由 versal possible-image family 的 saturation（G0）和 C-data isomorphism 的 measure descent（G1/G3）推出，而不是由 ring isomorphism 推出。该 reduction 是 conditional valid；当前 source 没有 G0/G3，故 unconditional TC 不能从现有数据推出。TC-A..H/TC-S 仍缺；没有 arbitrary containment/volume equality。

下一步最小任务：

1. 在 IUT III Cor3.12 的 exact definition 中形式化 `U_C` 是否就是 full Ind1/2/3 versal family（G0）；
2. 对 C_K/C_F/V/ε 构造 canonical normalized measure，并证明 C-data iso 的 c=1 或算出 c（G3）；
3. 只对 fixed row/place/Θ/gluing 计算 `nu_source(L)`，再代入 `nu(H_C)≥c·nu_source(L)`；
4. 若 G0 失败，给出固定 component 的反例或 no-go；不要扩大 H_C。

## 9. 状态

Stage1 natural-language/geometry only；无 Lean/Project/kernel/comparator/独立审查；target_accepted=false；P6 open。没有把 G0-G3 当作已证 source theorem；没有 arbitrary data 或 fabricated closure。

