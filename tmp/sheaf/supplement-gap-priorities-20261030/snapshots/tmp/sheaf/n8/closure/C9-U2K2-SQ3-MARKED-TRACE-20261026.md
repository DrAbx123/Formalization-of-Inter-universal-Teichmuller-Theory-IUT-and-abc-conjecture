# Fixed-C trace from `U2 K2` to the sQ3 q-mark

Date: 2026-10-26. Scope: one fixed admissible source datum `C`; follow the q-pilot mark through the IPL composite, and try to attach it to the actual sQ3 hull-determinant output with its original localization and readout. This is a bounded source trace, not a new abstract carrier or a claim that xi-f has been independently proved.

Source text checked: `tmp/sheaf/n8/closure/sources/IUT-III.txt`, SHA256 `822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D`.

**阅读入口更正（本轮用户要求边写边验、先查历史）：** §§1–5 保留推导历史；其中通用运输公式没有在固定真实 `C` 上完成实例化，不能读作已经交付实际 local maps。§6 登记本轮重复了哪些旧尝试；§7 更正 localization 的类型、cQ3 对象与受限输出族的区别。没有新增 C1 证明。

## 1. The part that does transport

Fix `C`, its q-pilot prime-strip, the splitting generators `eta_q`, and the local comparison data in the Remark 3.10.2 diagram. Write the three lower arrows as `L0,L1,L2`, the three upper arrows as `U0,U1,U2`, and the vertical arrows as `K0,...,K3`. With right-to-left composition, commutativity says

```text
U_i K_i = K_{i+1} L_i.
```

The IPL composite described in Remark 3.11.1(iii) is

```text
U2 U1 U0 K0 L0^-1 L1^-1.
```

The first square gives `U0 K0 L0^-1 = K1`; the second gives `U1 K1 L1^-1 = K2`. Hence the composite is exactly `U2 K2`. This is cancellation in the coherently chosen full-poly-isomorphism diagram, not a choice of unrelated representatives.

Let `Phi = U2 K2`. For actual coherent components of this source isomorphism, its effect on the marked data is the transported mark

```text
eta'_v = Phi_v(eta_q,v).
```

The component/naturality formula for a localization is recorded conditionally in §7.1; this file does not instantiate all its components on a specific `C`.

The full prime-strip map has global and local components. On the q side, their localization square is

```text
Q_global  --Phi_global-->  Q'_global
   | loc_q,v                  | loc'_q,v
   v                          v
Q_v      --Phi_v------->     Q'_v
```

or, as an equation, `Phi_v o loc_q,v = loc'_q,v o Phi_global`. If `t^q_ij : Q_i -> Q_j` are transition maps for local representatives of the marked object, the transported transitions are `t'_ij = Phi_j t^q_ij Phi_i^-1`. Their cocycle is inherited:

```text
t'_jk t'_ij
= Phi_k t^q_jk Phi_j^-1 Phi_j t^q_ij Phi_i^-1
= Phi_k t^q_ik Phi_i^-1
= t'_ik.
```

Thus the source's coherent full-strip isomorphism transports the q-marked isomorphism class. The cancellation itself proves no new local/global sheaf cocycle, and this file does not instantiate such a cocycle for a specific `C`. It gives no map from the transported mark to the sQ3 hull determinant.

## 2. Where sQ3 supplies maps, and their domain

For each actual allowed output region `D` of this same `C`, let `H_C` be the paper holomorphic hull. The inclusions `D_v -> H_C,v` are the local structure maps described by sQ3/cQ3 after the allowed determinant power `M_C` is taken. The corresponding objects carry the local/global localization data in the codomain Frobenioid. For these actual `D`, cQ3 supplies the structure-poly-morphism orbit to the hull object, and the localization data glue the local output objects to their global object.

To use this for the transported q-mark, one must instantiate that construction with the same marked object, not merely an isomorphic object in the ambient prime-strip. The required data would be

```text
u_q,v : Q'_v -> det^M_C(H_C,v)
g_q   : Q'_global -> det^M_C(H_C)

u_q,v o loc'_q,v = loc_H,v o g_q
u_q,j o t'_ij = t^H_ij o u_q,i
```

and a proof that the resulting marked collection is in the original restricted sQ3/final-evaluation family. This is the first point where the construction stops: the preceding IPL map has codomain the transported prime-strip data, while cQ3's map has domain an object already admitted to its hull-structure collection. No source constructor identifies `Q'_v` with such an admitted output object or constructs `u_q,v` and `g_q` for it. Defining `D := Phi(eta_q)` and then using the generic sQ3 map would assume the missing output-family membership.

## 3. Normalization check

Freeze the source's common positive tensor power `M_C`, the original `O(-)` reference `R_C`, the original place/label weights `w_(v,j)`, and the signed readout `nu_C`. The target comparison is a map into the determinant of `H_C` measured against this same `R_C`; it is not enough to compare two objects after independently changing their references. `Phi` transports the q-pilot structure, but the required sQ3 attachment must still identify its transported reference with `R_C` (or compute the actual relative-index correction) and then prove

```text
nu_C(Q'_C) = Q_C
```

or give a source-produced family `Q_C - eps <= nu_C(D_eps) <= h_C` with the same `M_C`, reference, weights, and readout. No such `D_eps` or readout map is produced by the `U2 K2` cancellation. cQ4 and the later log-volume/degree comparison transport a comparison once its objects and references are identified; they do not fill the missing q-to-hull structure map.

There is also a target-strength distinction: xi-d defines `R_{<= -log(Theta)}` to be the real half-line `{x | x <= -log(Theta)}`, not the image of the restricted actual output family. xi-f's paper-level scalar assertion, if accepted as a source theorem, yields the inequality without exhibiting the marked object demanded here. It therefore cannot be cited as a construction of the above `u_q,v`, `g_q`, or output-family member.

## 4. Exact interface boundary

- `SourceKummerEvaluationArrows.lean` freezes reduced `FPrimeStripEquiv` representatives and a separate unit layer. Its `sourceKummerArrow_self` and `sourceEvaluationArrow_self` are identity/trivial-action satisfiability witnesses, not the source arrows for `C`.
- `SourceKummerEvaluationSquareExtension.ofThreeArrows` constructs a commuting strip square from an already supplied upper evaluation arrow and two Kummer arrows. Its target is still a prime-strip square; it has no hull determinant, q-mark, output-family membership, or readout.
- `SourceTheorem311Realization` carries procession, packet, vertical, and evaluation data in the reduced `Choice` interfaces. It does not carry the paper full-poly-isomorphism's marked q-object together with an sQ3 output.
- `C9IUTBridgeOutput.C1SourceBridge` stores `qPilotOutput_mem` as an explicit field. It does not derive that membership, and its `possibleOutputs` is a singleton reference-output class, not the paper's restricted multiradial output family.
- `SourceArithmeticHolomorphicLanding` has reduced localization-reading records, but no constructor connecting the transported q-mark to the actual hull determinant.

The relevant source-level definitions and limitations are documented at `SourceKummerEvaluationArrows.lean:200,290,347,418`, `SourceKummerEvaluationSquareExtension.lean:90`, `SourceHodgeTheaterBridge.lean:730,910`, `SourceFaithfulBoundary.lean:270`, `SourceArithmeticHolomorphicLanding.lean:210,243`, and `C9IUTBridgeOutput.lean:76`. The paper statements are IUT III Remark 3.10.2 (`IUT-III.txt:8917`), Remark 3.11.1(iii) (`:9461, :9544`), sQ3/cQ3 (`:8183, :8264`), and xi-d--xi-f (`:10641, :10682, :10705`).

## Result

The source asserts transport of the q-marked full-strip isomorphism class and separately asserts a formal-quotient closed loop preserving both intertwinings. This note has not expanded either assertion into actual fixed-`C` local/global maps or a descent cocycle. It does not construct the q-marked sQ3 structure morphism, a member of the restricted final-evaluation family, or the frozen `M_C`/`O(-)`/weights/readout comparison. No source constructor is exposed by the current Lean interfaces. Do not add these items as free fields. C1 remains open at the independent-construction level.

Validation: paper-text and interface inspection only. No Lean compile, Project build, comparator, or independent review was run.

## 5. Working derivation and failed lift (2026-10-26)

This section records an attempted construction while checking its types. It is not a proof of C1.

Fix one admissible `C`. Let `Q` be its q-pilot object, `Q'` the transported q-pilot after `Phi = U2 K2`, and `H` the hull determinant of the restricted actual output family for this same `C`. The already constructed maps have types

```text
Phi_global : Q_global -> Q'_global
Phi_v      : Q_v      -> Q'_v
loc_Q,v    : Q_global -> Q_v
loc_Q',v   : Q'_global -> Q'_v
```

with `Phi_v ∘ loc_Q,v = loc_Q',v ∘ Phi_global`, and the transported transitions satisfy the cocycle. The desired new maps have different codomains:

```text
g       : Q'_global -> H_global
u_v     : Q'_v      -> H_v
loc_H,v : H_global  -> H_v
```

and must satisfy both `u_v ∘ loc_Q',v = loc_H,v ∘ g` and the transition compatibility. The IPL square only relates `Q` and `Q'`; it has no `H` in its types. The sQ3 structure maps have source an admitted actual output object and target `H`; they do not have source `Q'` merely because `Q'` lives in the same ambient Frobenioid.

The tempting definition `g := (sQ3 structure map for Q')` is ill-typed at the source-family boundary: that structure map can be selected only after proving that `Q'` is one of the allowed output objects. Defining an output `D := Q'` does not establish `D ∈ P_C`; it changes the meaning of the restricted algorithm output family. Defining `D` to be an actual output and postulating an identification `alpha : Q' ≅ D` also leaves the substantive obligation: construct `D` and `alpha` from the fixed `C`, with the specified `M_C`, reference, weights, and readout. Thus the proposed lift does not advance the proof and is withdrawn as circular.

The remaining constructive test is not “do the two carriers inhabit a common category?” but the following concrete source obligation for the fixed `C`:

```text
there exist an actual D in P_C,
  a marked identification alpha : Q' -> D,
  and the sQ3 map i_D : D -> H,
such that (i_D ∘ alpha) commutes with the original localizations
and transitions, and its readout uses M_C, R_C, w_C, nu_C.
```

This implication is useful only if `D` and `alpha` are built from earlier data, not supplied as fields of the conclusion. Until such a construction is written down, `u_v := (i_D)_v ∘ alpha_v` is just composition notation for the missing map.

One normalization issue remains in the earlier generic transport display. `rho_v` is a localization map between a global and a local object, whereas `Phi_v` acts on the local object and `Phi_global` on the global object. Therefore `Phi_v ∘ rho_v ∘ Phi_v⁻¹` is generally ill-typed. The natural transported localization is instead

```text
rho'_v = Phi_v ∘ rho_v ∘ Phi_global⁻¹,
```

provided the two `Phi` components are actual isomorphisms with the indicated domains. Its naturality equation is then a typed square. This correction affects only the displayed generic transport formula; it does not create a map to `H`.

## 6. 历史复用与本轮重复工作登记

日期：2026-10-26；负责人：root，单 agent。实际消费者：`n8-c9-final-evaluation-capsule` / `FinalEvaluationQMark`。阶段：SHEAF stage 1。用户要求先查已做内容并做笔记；本节属于证据整理，不计为数学缺口减少。

| 本轮提出或重查的论证 | 已有记录与位置 | 继续使用时的判定 |
|---|---|---|
| final evaluation 给出 further rigidifications，故其中包含固定 q-rigidification | [FULL-TH310-BASIS](C9-C1-FULL-TH310-BASIS-20261025.md) §2、§4，原句在第44、64行 | 旧正向推论，尚未证明。不能再次作为新入口或已证依赖。 |
| 把 q 的成员性写成 `Theorem311Full.qPilotOutput_mem` | [THREE-TRANSPORT 审查](C9-REVIEW-THREE-TRANSPORT-20261025.md) §2–§6 | 已指出该字段额外输入了目标成员性；编译通过不会证明字段的来源。该审查针对旧包装，不是完整 IUT 的独立性证明。 |
| `various possibilities`、q-coricity、函子性足以给出指定 q 标记 | [MARKED-GATE-RECHECK](C9-C1-MARKED-GATE-RECHECK-20261026.md)，尤其第83–86行；[CARRIER-ONE-SIDED-REUSE](C9-CARRIER-ONE-SIDED-REUSE-20261026.md) §10.3 | 后续记录已撤回这一步；本轮再次提出是重复尝试。 |
| 闭环经过 sQ3/sQ4，于是 q 自动成为实际输出 | [C1-LOOP](C9-C1-LOOP-20261025.md) §4–§7；[CARRIER-ONE-SIDED-REUSE](C9-CARRIER-ONE-SIDED-REUSE-20261026.md) §4.1、§10.3 | 已尝试，未给出对象成员及读数见证。旧文的“不可导出/独立”字眼不能提升为完整源理论的逻辑结论。 |
| cQ3 的 local-global collection 自动给全局 q-to-hull 比较 | [LOCAL-GLOBAL-DESCENT](C9-LOCAL-GLOBAL-DESCENT-ATTACK-20261024.md)；[MARKED-IMAGE-DESCENT](C9-MARKED-IMAGE-DESCENT-20261024.md) | 已排除这个弱推理；其中局部算术例不是完整 IUT 反例。本轮不重新跑它。 |
| xi-e 的固定 q 可执行性，直接推出 xi-f 的读数结论 | [XIE-SOURCE-CONDITION-AUDIT](C9-XIE-SOURCE-CONDITION-AUDIT-20261026.md)；[XIE-XIF-7DAY-RECHECK](C9-XIE-XIF-7DAY-RECHECK-20261026.md) | 既有区分继续有效；原文内部的证明性断言与本仓库独立完成的证明必须分开。 |
| 将 `R_{≤h}` 当作实际输出读数集合，再把 exact attainment 称为原文结论 | [HANDOFF-SUMMARY](C9-C1-HANDOFF-SUMMARY-20261026.md) 末节；本笔记 §3 | 已更正：xi-d 定义的是半直线。exact / signed actual-output witnesses 是充分证书；尚未证明是原标量目标的必要条件。 |

本轮已读上述相关记录以及原文 cQ3、Remark 3.11.1(iii)、xi-c–xi-f。没有发现新的源 constructor。刚才再次把“final evaluation 构造 further rigidifications”称为新入口，以及打算再检查“闭环是否多给一个箭头”，均未超出已审查论证；不计为新进展，也不再把它们列为下一项泛查任务。

原文强度也须保留：Remark 3.9.5(viii) 描述 projection 的目标；(ix) 断言在 formal quotient indeterminacies 下闭环，并明确谈到同时带 Θ- 与 q-intertwining 的结构。不能说原文完全没有兼容性断言。但重引该断言并未独立展开本任务要求的固定 `C` 的实际标记比较。这里既没有证明原文错误，也没有证明完整源假设下 C1 独立或不可判定。

## 7. 对本笔记映射类型与完成口径的更正

### 7.1 通用运输公式不算实际固定-C构造

§5 的 “The already constructed maps” 表述过强，现撤回：本文件写下了给定相干同构后应满足的公式，没有交付从固定真实 `C` 得到的具体分量。Remark 3.10.2 的方形消去可复用；它本身不是到 hull 的箭头。`t'ij = Phi_j t_ij Phi_i⁻¹` 的 cocycle 验算也以既有、相容的 `t_ij` 为前提；本轮没有构造源对象的覆盖/重叠数据，不能把不同算术地方自行当作一个开覆盖。

§1 的 `rho'_v = Phi_v rho_v Phi_v⁻¹` 没有先核实纸面 `rho_v` 的域与陪域；§5 又径直称该 `rho_v` 为 localization map，这同样未经定义核验，现撤回这项认定。下面单独使用 `lambda_v` 表示 cQ3 的 localization **isomorphism**，不冒认它就是原文 `rho_v`。

cQ3（本地原文第8311–8316行）给的是局部对象的 realification 与全局对象的 localization 之间的同构。因此采用下述方向的记号：

```text
real_v : C_local,v -> C_local,v^R
Loc_v  : C_global  -> C_local,v^R
lambda_v : real_v(L_v) ≅ Loc_v(G)
mu_v     : real_v(H_v) ≅ Loc_v(H_global).
```

对于候选局部/全局态射 `u_v : L_v -> H_v`、`g : G -> H_global`，需检查的方形是

```text
mu_v ∘ real_v(u_v) = Loc_v(g) ∘ lambda_v.
```

两边的域都是 `real_v(L_v)`，陪域都是 `Loc_v(H_global)`。直接写 `Q_global -> Q_v` 会隐藏 localization functor 和 realification，不能当作原文已经存在的内部态射。

如果另外已经给定同构 `alpha_g : G ≅ G'`、`alpha_v : L_v ≅ L'_v`，运输公式才是

```text
lambda'_v = Loc_v(alpha_g) ∘ lambda_v ∘ real_v(alpha_v)⁻¹.
lambda'_v ∘ real_v(alpha_v) = Loc_v(alpha_g) ∘ lambda_v.
```

第二式由第一式消去逆元得到。这是有明确前提的类型/代数验算，不是构造了本任务的 `g` 或 `u_v`，也不关闭 C1。

### 7.2 cQ3 对象不按定义等于实际输出

§§2、5 的说法须细化。cQ3 的局部 ⊼-category 对象，是带有到指定 hull determinant 的 linear structure-poly-morphism 的局部 Frobenioid 对象；原文还提出可限制到 hull-approximants 的版本。**它不按定义等于实际 final-evaluation 输出族 `P_C`。** 实际 multiradial output 的对象层进入 hull 比较，是 cQ3 讨论的用途；反过来，任意具备这类结构态射的对象未必是实际算法输出。

因此 `g := (sQ3 structure map for Q')` 的问题是没有给出所调用的结构态射，也没有证明 q-object 已被构造成此 ⊼-category 中的对象。可以尝试直接从源数据构造该态射；不能说必须先证明 `Q' ∈ P_C` 才允许尝试。若还要交付用户要求的受限输出成员性，则需另外核实对象的实际算法来源。两项责任不得互相替代。

§5 的 `alpha : Q' -> D` 也只是草图：`D ∈ P_C` 若表示一个 IQ 区域，它并非 q-pilot 所在范畴中的线对象。写 `L_C(D)` 表示将 `D` 送入同一 `M_C`、inverse-reference、weights 下的输出 determinant/hull construction 后，候选类型才可能是

```text
alpha : Q' -> L_C(D)
i_D   : L_C(D) -> H_det,C
g     := i_D ∘ alpha.
```

若称 `alpha` 为 marked identification，还须证明相应同构及标记/读数相容，普通箭头不能自动充任。这个复合式只对已经构造的 `D`、`L_C(D)`、`alpha` 有意义；本轮没有提供这些 fixed-C见证。

### 7.3 后续复用约束与真实状态

本轮交付是：重复路线索引、失效推论撤回，以及映射类型的更正。它没有减少 C1 的未证数学责任。沿原任务继续时，只在能指出具体源定义/引理并实际构造此前没有的固定-C映射或标记见证时推进；不得把上表旧路线换名字再次汇报为发现。若仍无 constructor，按用户原限定停在这里，不自动转去数值、IPL、抽象 sheaf 或重证 A1/A2/A3。

`statement_compiles`: not applicable (documentation only); `proof_body_checked`: not run; `kernel_closed`: not run; C1 `proof_status=open`; `target_accepted=false`。本轮未运行 Lean、Project、comparator 或独立审查，未改 Lean 定义，未构造完整源反例。
