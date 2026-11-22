# C9 new source theorem：integral polarization TC1

任务：task-251（New source theorem: integral polarization TC1）。owner：iplsheapt。日期：2026-10-25。自然语言 source-theorem 尝试；不改 Lean/Project/目标；不引入 arbitrary data/assumption；只写本文件。

输入：Kondo 2025/2026 本地快照（sources/Kondo-2512.09231v1.html, sources/Kondo-2605.25428v2.html）；C9-NEW-TANNAKIAN-TRACE-20261025.md（task-242）；C9-ADJUDICATE-HAFULL-20261025.md（task-203）；C9-TRACE-SYMPLECTIC / C9-U-LINE / C9-U-ORTHOGONAL；AbsTopIII 相关定义。

状态：没有 Lean/Project/kernel/comparator/独立审查；P6 open；target_accepted=false。

## 0. Verdict

TC1 **没有** 从 frozen source 建立。本文件给出三个新的精确结果：

1. **Conditional N4 theorem（新）**：若 H 通过 tensor automorphisms 作用、保持 trace form `beta_T`，固定 U 并在 W 上不可约，则 `U=W^⊥_beta=Q_p1`；于是 1∈U、H_A-full、B=O_K。这把 N4 归约到 N1 + beta-invariance。
2. **N3 obstruction（新）**：若 `beta_T` 是 actual trace form `Tr(xy)`，`Omega_T` 是 primitive Kondo/surface intersection form，则 `J=beta_T^{-1}Omega_T` **不是 integral endomorphism**；在 W 的 π-power basis 中 `beta|W` 是 anti-diagonal `c=41p u`，`beta^{-1}` 含 `1/c`，故 `J` 有分母 41p。要救 integrality 必须把 Omega 乘以 41p，破坏 primitive Kondo form；这不是 source normalization。
3. **Parity impossibility（新）**：V=K 为41维奇数，alternating Omega 在 V 上必退化；若只定义在 W 上并令 U⊥W，则 Omega(1,·)=0，J(1)=beta^{-1}Omega(1)=0，与 TC1(e) J(1)=1 矛盾。故 TC1(a)-(e) 作为原 statement 已是 internally inconsistent。
4. **N1/N2/N5 status**：N2/N5 可在 abstract standard representation of Sp40 上构造（unique invariant alternating form + U⊥W extension），但没有 source tensor functor；N1 的 outer-automorphism-to-tensor lift 未给；N4 的 full source version 仍缺。

因此没有 `U=W^perp`、1∈U、H_A-full、B=O_K 的 source theorem。

## 1. TC1 的精确内容

TC1（modified integral Tannakian conjecture）要求 neutral integral Tannakian category T with fiber K，distinguished V，并且：

```
(a) W_T fiber W=ker Tr, Omega_T = Kondo Sp40(Z_p)-alternating form;
(b) Sp action by tensor automorphisms, Omega_T-symplectic;
(c) U/W decomposition Omega_T-orthogonal: U_T=W_T^perp;
(d) trace-canonical line L_T=Q_p1, i.e. 1 in U_T;
(e) J=beta_T^{-1}Omega_T integral, J(L_T)=L_T (or J(1)=1).
```

若 TC1 成立，Theorem 3.1（task-242）给 `U=W^perp`、1∈U、H_A-full、B=O_K。下面逐项 attempt。

## 2. 实际 trace form 与 U_beta

K/Q_p tame totally ramified e=41, p=12301, O_K=Z_p[π], π^41=p u, J=m, W=ker Tr。Trace table：

```
Tr(1)=41,  Tr(π^a)=0  (1≤a≤40).
beta(x,y)=Tr(xy)  symmetric nondegenerate;
beta(π^a,π^b)=41 p u if a+b=41, else0  (1≤a,b≤40).
```

因此 `W^⊥_beta=Q_p1`：1 与 W 配对为0，beta(1,1)=41≠0；dim W=40，nondegenerate ⇒ W^⊥ 是1维，即 Q_p1。**这是 actual**。

但 Kondo/Sp 的 fixed line U 未必等于 Q_p1；task-203 已裁决 W 是 Q_p-hyperplane，U 是任意 complement 的 fixed line，不能把 U 直接设为 trace line。TC1(d) 正是要把两者等同。

## 3. New conditional theorem：tensor beta-invariance ⇒ U=Q_p1

**Theorem N4-T (conditional, genuine group-theoretic lemma).** 设

```
(i)  H acts on V=U⊕W by tensor automorphisms preserving beta_T;
(ii) H acts trivially on U and irreducibly on W;
(iii) beta_T|W is nondegenerate and W=ker Tr (codim1).
```

则 `U=W^⊥_{beta_T}=Q_p1`，故 `1∈U`，`H_A-full`，`B=O_K`。

证明：对 u∈U,w∈W，`beta_T(u,w)` 是 H-invariant bilinear pairing；H 在 U 上 trivial、在 W 上 irreducible 且非平凡，故 invariant linear map `W→U*` 必为0；所以 U⊂W^⊥。beta_T nondegenerate、W codim1、U∩W=0 ⇒ U=W^⊥。再由 trace table `W^⊥_beta=Q_p1`，得到 U=Q_p1。条件 (iii) 使 `W=ker Tr` 与 beta 的 orthogonal complement 对齐。QED

这个定理是 TC1 的 **conditional core**：它不需要先假设 `1∈U`，而是从 tensor beta-invariance + irreducibility 推出。缺的是 (i)/(ii) 的 source：N1 tensor action + N2 Omega? 注意 N4-T 只用 beta，不用 Omega；它还需要 H 作用在 U/W 上的结构。Kondo 2026 的 H=Φ^{-1}(Sp) 作为 outer automorphism subgroup 给 W 上的 Sp action，但 **outer automorphism 不自动给 tensor automorphism**（N1）。

如果 N4-T 的前提成立，TC1(d) 就已证；剩下 N3 integral J 和 Omega。

## 4. N2/N5：abstract Sp polarization 可以构造，但只是 abstract

对 abstract group Sp_{2g}(Z_p) 的 standard representation W（dim 2g=40）：

```
Omega_std: Λ²W → Q_p,  integral primitive alternating, Sp-invariant;
unique up to scalar (standard representation irreducible).
```

给定 H→Sp 的 homomorphism，可把 Omega_std 拉回 W 上；再在 U⊕W 上定义 `Omega(u,w)=0`, `Omega|W=Omega_std`, `Omega|U=0`，得到 N2/N5 的 **abstract construction**。这个构造是 genuine algebraic theorem，但**不是** source theorem：

- H→Sp 只是 Φ(H)=Sp 的 abstract quotient，不是 tensor functor；
- `Omega_T` 与 IUT 的 log-shell/theta-pilot metric/volume 没有 identify；
- integrality/primitive normalization 与 surface intersection form 的 identification 未给。

所以 N2/N5 的 **abstract model** 完成；source-level 仍缺。

## 4.5 Parity obstruction：Omega 在 V=K (dim41) 上不可能 nondegenerate

这是一个比 N3 更基本的 **TC1-as-written impossibility**。

```
V=K has Q_p-dimension 41 (odd); U=Q_p1 dim1, W=ker Tr dim40;
an alternating form on an odd-dimensional Q_p-vector space is degenerate;
TC1 only puts Omega_T on W_T (dim40) and declares U orthogonal to W.
```

因此 TC1 的 `Omega_T` 若作为 V 上的 alternating form 扩展，必有非零 radical；若只定义在 W 上并在 V=U⊕W 上令 U⊥W、Omega|U=0，则

```
Omega(1,·)=0  ⇒  J(1)=beta_T^{-1}Omega(1)=0,
```

与 TC1(e) 的 `J(1)=1`（或 `J(L_T)=L_T`）矛盾。即使 beta_T 换成任意对称 nondegenerate form，只要 Omega 是 alternating 且 U 是 1 维 orthogonal complement，`Omega(1,·)=0`，所以 `J(1)=0`。

**结论**：TC1(a)-(e) 作为同一个 theorem 是 **internally inconsistent**；要修正只能：

```
(P1) J 只定义在 W 上（而不是 V 上），L_T 与 J 分开；或
(P2) 把 U/W 改为 even-dimensional V'（例如去掉 U 后只在 W 上工作）；或
(P3) 使用非 alternating / degenerate 的 'polarization'（已不再是 integral symplectic polarization）。
```

这三种都不是原 TC1；P1 无法给 `1∈U` 的 J 证明，P2 不能覆盖 U，P3 违背 TC1 的 alternating 要求。故原 TC1 的 final conclusion 不能从 source 建立，且在形式层已不可能。

## 5. N3 obstruction：trace beta + primitive Omega 的 J 不 integral

取 W 的 π-power basis `(π,...,π^40)`；beta|W 的矩阵 B 是 anti-diagonal：

```
B_{a,b} = 41 p u  if a+b=41,  else 0;      c:=41 p u.
```

B 可逆，`B^{-1}` 的 entries 含 `1/c`。若 `Omega_T` 是 primitive integral Kondo/surface intersection form（在某 symplectic basis 中矩阵有 unit entry），则

```
J = B^{-1}·Omega_T
```

至少有一个 entry 分母含 c=41p u；p=12301∤? 41p u 不是 Z_p unit。故 `J∉End_Zp(O_K)`，`J(L_T)⊄L_T`。

**精确反例（dim2 model）**：若 `B=[[0,c],[c,0]]`、`Omega=[[0,1],[-1,0]]`，则

```
B^{-1}Omega = (1/c)[[-1,0],[0,1]],
```

不是 integral。W 的40维 anti-diagonal B 给同样结论：J 的某些 entries 必含 1/(41p u)。

要令 J integral，必须把 Omega 乘以 c（或至少41p）；但这改变了 primitive Kondo form 的 integral normalization。TC1(a) 指定 Omega_T 是 Kondo Sp-form；若 Kondo form 仅定义 up to scalar，选择 c 倍是一个额外 normalization，不是 source theorem；若要求 primitive/unimodular，TC1(e) 直接失败。

因此：**TC1(e) 对 actual trace beta + primitive Kondo Omega 是 impossible**；只有把 beta_T 换成另一个非 trace symmetric form，或把 Omega 非 primitively rescale，才可能。两者都不是当前 source。

## 6. N1：为什么 outer action 不是 tensor action

Kondo 2025：`rho: Mod(S minus P) → Out(G_K)` 是 set-theoretic map，不是 homomorphism。Kondo 2026：`H=Φ^{-1}(Sp_{40}(Z_p)) ⊂ Out(G_K)`，`Φ(H)=Sp`；`H` 是 outer automorphism subgroup，不是 `Rep(G_K)` 的 tensor automorphism group。

要从 H 得到 tensor autoequivalence of `Rep(G_K)`，需要：

```
N1a. a lift/section H→Aut(G_K) (or a coherent 2-cocycle/obstruction) — not in source;
N1b. a tensor functor from the mapping-class/Sp source to T — not in source;
N1c. compatibility with Kondo's Φ and with the Tannakian fiber K — not in source.
```

Outer automorphisms act on representations only up to inner isomorphisms; inner automorphisms give natural tensor isomorphisms, but a coherent strict action needs the lift. The source does not supply H²(H,G_K) or a splitting. Hence N1 missing; N4-T cannot be applied to H. 

## 7. N4/N5/N2/N3/N1 classification

| item | status |
|---|---|
| trace beta, W=ker Tr, W^⊥_beta=Q_p1 | PROVED actual |
| N4-T: tensor beta-invariance + irreducibility ⇒ U=Q_p1 | PROVED conditional |
| N2 abstract Sp-invariant Omega_std | PROVED abstract |
| N5 abstract U⊥W extension | PROVED abstract |
| N1 tensor functor/lift from Kondo H | MISSING |
| N2 source-level Kondo Omega_T/metric | MISSING |
| N3 integral J=beta^{-1}Omega with primitive Kondo Omega | IMPOSSIBLE (trace beta) |
| N4 source-level U=Q_p1 | CONDITIONAL on N1 |
| TC1 as written (U∧1 with Omega_U) | IMPOSSIBLE (parity obstruction) |
| TC1 full | NOT PROVED / inconsistent as stated |
| H_A-full/B=O_K | NOT OBTAINED |

## 8. 如果 TC1 established 会得到什么

若未来 source 给出 N1/N2/N3 的替代（例如非 trace beta_T 或 non-primitive Omega normalization）并满足 N4-T/N5，则 Theorem 3.1 给

```
U=W^perp,  1∈U,  H_A-full,  B=O_K.
```

但当前没有：N3 obstruction 阻止 trace beta；N1 阻止 tensor action；N2 source Omega 缺。不能把 abstract Sp model 当作 Kondo/IUT source。

## 9. Conclusion

本文件给出一个 genuine conditional theorem（N4-T）和两个 genuine obstruction（parity obstruction; N3 trace-vs-primitive-Omega）；N1/N2/N5 的精确缺失也定位。TC1 **as written 已 internally inconsistent**（V 奇数维 + U⊥W 导致 J(1)=0 与 J(1)=1 矛盾），因此更不可能从 Kondo 2025/2026/AbsTopIII 当前快照建立：

```
trace beta is symmetric with beta|W anti-diagonal c=41pu;
primitive Omega forces J=beta^{-1}Omega to have denominator c;
outer H has no tensor lift;
unique Sp form exists only abstractly, without source metric/log-shell identification.
```

因此 U=W^perp、1∈U、H_A-full、B=O_K 仍不能 source-level 得出；TC1 若要继续，必须先修正 P1/P2/P3 中最少一项，离开原 statement。没有 arbitrary assumption；没有 Lean/Project edits；P6 open。

