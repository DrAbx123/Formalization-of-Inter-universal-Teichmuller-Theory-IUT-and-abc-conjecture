# C9 独立算术/依赖审计：b=3, 273, 1347 与全局装配

任务：task-158（C9 independent arithmetic/dependency audit）。owner：iplsheapt。日期：2026-10-25。自然语言/精确有理数审计；不改 Lean/Project，不改目标，不新增攻击命题。只写本文件。

审计对象：

- C9-UNIFORM-HULL-20261025.md, SHA256 99539B279B008CBEE367C14BC48AC11114460B0C0B706A71546FFDDC245A7D5B
- C9-GLOBAL-ASSEMBLY-20261025.md, SHA256 6AB115790D8CDFD9E261985F7F209E4817C572AF6AAF4A48EB0EFDC2DE52CCF2
- C9-ARCHIMEDEAN-20261025.md, SHA256 F4C7AFE112C238D7F5547461C1500AC45A73E49075BDDF366FE8B1E5A53E9957
- C9-TAME-LOG-DOMAIN-20261025.md, SHA256 23B3514B94972DE511F1B17E23AB3DA832ED5BC63E89DACA3875ADEB07961F06
- C9-SYMPLECTIC-SOURCE-20261025.md, SHA256 3F98F68A5E143DCD51ED6790B1C839AE7B8811E4E418D48B02E37E7C4D5B9C70
- C9-IND1-GLOBAL-20261025.md, SHA256 94785726EE890F6BC672861C570238F040636A6273A7722B2621949C48AF9AB8
- C9-MODP-CERTIFICATE-20261025.md, SHA256 E5056D524DA94683E5B6BA765EA0AEAF8B23C03D96814F02B49CB47496CC9E95

状态：stage1 独立审计。没有 Lean/Project/kernel/comparator/独立审查；没有完成 P6。target_accepted=false。

## 0. 执行结论

1. b=3, b=273, b=1347 的**有理数算术**全部复核通过（误差为0）：`Σs_j`、`h_A`、`h_B`、`Q_p`、`Q_p−h` 与文档中的精确分数一致（见 §1）。这是本审计的 arithmetic-valid 核心。
2. 这些数值的**实际来源**不是 paper-level：`h_A` 的 “aligned actual hull” 依赖 TAME §5 的 (11)–(14)；task-149 已把 (11)–(14) 标为 withdrawn，并要求 TC-A..TC-H/TC-S。`h_B`/B=I 依赖 corrected symplectic donor + basis alignment；task-155 的 MODP 证书只在 inferred alignment 下给 B=O_K，B=I 不是 actual。
3. C9-GLOBAL-ASSEMBLY 的 W1 权重与 G4 代数恒等式可独立复核；但 G1/G6 的 “h_C ≥ ... / Q_C−h_C ≤ ...” 是条件装配，不是原目标 h_C≥Q_C 的证明。
4. C9-ARCHIMEDEAN 的 paper-level arch 上界 `((l+5)/4)logπ` 与符号/换算复核通过；但 §4 的 b=273 行把 B 分支 `−38736/41` 写成了 h_p；actual B=O_K 分支是 `−39156/41`。该行数值本身对 B 分支成立，但作为 “finite bad h_p” 是 invalid label；结论（arch-only 不足）在 correct A 值下仍成立且更强。
5. 所有依赖 corrected donor 的 orbit/volume/target containment 均降级：conditional 或 invalid as target proof。没有新的 global attack 结论。

## 1. 独立精确重算

约定：`e=41, m=20, c=20/41`；uniform `ρ=1`，

```
s_j = floor(b j²/41), b j² = 41 s_j + t_j, 1≤t_j<41;
h_A = −(1/20)Σ(s_j + 1/41) = −(41 Σs_j + 20)/820;
h_B = −(1/20)Σs_j + (1/20)Σj − (1/20)Σ(j+1)/41
    = (−41 Σs_j + 8380)/820;
Q_p = −b/41;     D_A = Q_p−h_A;   D_B = Q_p−h_B.
```

### 1.1 Uniform ρ=1: b=3,273,1347

| b | Σs_j | h_A | h_B | Q_p | Q_p−h_A | Q_p−h_B |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 200 | −411/41 | 9/41 | −3/41 | 408/41 | −12/41 |
| 273 | 19100 | −39156/41 | −38736/41 | −273/41 | 38883/41 | 38463/41 |
| 1347 | 94280 | −193275/41 | −192855/41 | −1347/41 | 191928/41 | 191508/41 |

这些分数与 C9-UNIFORM-HULL §3.1/§3.2 完全一致；b=1347 的 uniform 行是本审计补算的（文档只给了 ρ=1/2 的 b=1347）。

对 b=3,273,1347 都有 `Σ t_j = 410`，故

```
T := (1/(41·20)) Σ t_j = 410/820 = 1/2.
```

### 1.2 General ρ=1/2: b=3,1347

`h_{1/2}(b) = −(1/20)Σ_{j=1}^{20} 2^{−(j+1)}(s_j+1/41)`；direct-domain `h_direct=h_{1/2}−23/2`；`Q_p=−b/82`。

| b | h_{1/2} | h_direct | Q_p | Q_p−h_{1/2} | Q_p−h_direct |
|---:|---:|---:|---:|---:|---:|
| 3 | −56311/10485760 | −120642551/10485760 | −3/82 | −13419889/429916160 | 4930615951/429916160 |
| 1347 | −51496081/10485760 | −172082321/10485760 | −1347/82 | −4950820039/429916160 | −6784199/429916160 |

符号核对：`Q−h<0` 表示 lower bound 已高于 `Q_p`（无亏损）；`Q−h>0` 表示仍有 deficit。因此 ρ=1/2 的 b=3 direct-domain 失败（gap 正），b=1347 direct-domain 成功（gap 负）；b=3/1347 的 zero-Kummer bound 都高于 Q_p。这些分数与 C9-UNIFORM-HULL §4 表一致。

### 1.3 G4 恒等式复核

C9-GLOBAL (G4) 写

```
D_p^Sp/log p = b(e+1)/12 − (b−1)/e − T,   T=(1/(e m))Σt_j ∈ [0,1).
```

代入 b=3: `3·42/12 − 2/41 −1/2 = 10.5−0.048780−0.5 = 408/41`；b=273: `955.5−272/41−0.5 = 38883/41`；b=1347: `4714.5−1346/41−0.5 = 191928/41`。三式与 §1.1 的 `D_A` 完全一致，代数有效。

## 2. 全局装配的符号/权重审计

### 2.1 权重

C9-GLOBAL 的 `α_v=[(F_mod)_v:Q_p]/[F_mod:Q]` 来自 III Rmk3.1.1(ii)/IV Rmk1.7.1 的 normalized weight，作为公式可接受；`Σ_{v|p}α_v=1` 是该 normalization 的内容。`ρ^{j+1}` 是 row/Θ 权重，`j=1..m`；不能把它和 `α_v` 混成一个权重。

`W2/W3` 的全局模板

```
h_C = Σ_p α_p h_p + Σ_{v|∞} α_v h_v,
Q_C = Σ_{p∈S_bad} α_p Q_p,   Q_p = −ρ_p b_p/e_p · log p
```

是**装配定义/模板**，不是完整 C 上已构造的对象；`h_v` 尤其没有 actual construction。C9-GLOBAL 自己也把它列为 inferred（§6 第7项），此审计确认该分类。

### 2.2 符号

- `Q_p<0`；`h_A<0`；`D_A=Q_p−h_A>0` 是 deficit。
- b=3 B 分支 `h_B=9/41>Q_p=−3/41`，`Q_p−h_B=−12/41<0`；这是**局部盈余**，不是实际目标证明。
- b=273 B 分支 `−38736/41` 仍低于 `Q_p`，`D_B=38463/41>0`。
- 任何把 `Q_p−h` 的符号反过来（说 `h>Q` 就是成功）都是错误的；本审计对每个分数显式计算。

### 2.3 C9-ARCH b=273 行的错误标注

C9-ARCH §4 表把 b=273 的 `h_p` 写成 `−38736/41`。该分数是 **B=I 分支** `h_B`；actual/conditional B=O_K 分支是 `h_A=−39156/41`。因此该行作为 “finite bad h_p” 是 invalid label。若改用正确 A 值，deficit 为 `38883/41`（更大），arch-only 不足的结论仍成立；但原表不能作为 b=273 的 h_A 引用。

## 3. 依赖：arithmetic-valid / conditional / invalid

### 3.1 Arithmetic-valid（给定公式后独立可复核）

A1. `Σs_j` 与 `h_A,h_B,Q_p,D_A,D_B` 的 b=3,273,1347 精确有理数。
A2. ρ=1/2 的 b=3,1347 精确分数与 gap 符号。
A3. `T=1/2`（这三个 b）与 G4 恒等式。
A4. `h_A` 在 uniform ρ=1 永不达到 Q_p 的代数论证：

```
h_A ≥ Q_p  ⇔ 41Σs_j+20 ≤ 20b;
s_j ≥ (b j²−40)/41,  Σ j²=2870
⇒ 41Σs_j ≥ 2870b−800 > 20b−20  (b≥1),
```

所以 A 分支对所有 b>0 都不闭合。B 分支的 `b≥4` 判定与 b=3 的直接值 9/41 也 arithmetic-valid。
A5. archimedean 上界数值：`(46/4)logπ≈13.164394` natural；`logπ/log43≈0.304403`，`logπ/log12301≈0.121554`；对应 `≤3.500052` 与 `≤1.397875` log p 单位。
A6. MODP 的 field-trace 算术：tame totally ramified、`Tr(π^a)=0 (1≤a≤40)`、`Tr(1)=41`、`I/J` 的 basis 与 trace line；这些是局部 tame 代数，不依赖 Kondo donor。

### 3.2 Conditional（继承 corrected donor/basis/target/Ind1）

C1. `h_A` 被称为 “aligned actual hull” 只在 TAME §5 的 source/target-container 步骤成立时；task-149 明确 (11)–(14) withdrawn，需 TC-A..H/TC-S，故 `h_A` 只能记为**条件性 aligned lower bound**。
C2. `h_B`/B=I 分支：task-155 MODP 在 inferred natural alignment 下给 B=O_K、`v=0`，B=I 不是 actual；`h_B` 的算术值只能作为 conditional branch value。
C3. C9-GLOBAL 的 G1/G6：`h_C ≥ ΣαH_p + h_∞`、`Q_C−h_C ≤ ...` 依赖 (11)–(14) 与 TC-A..H/TC-S；target containment withdrawn，故不能作为原目标 `h_C≥Q_C` 的证明。
C4. `J=m`、standard-lattice 分类、orbit generation (T7)、volume gain (T8)、`h_p`/`ν_A,ν_B`：均继承 task-147 的 inferred consequences，不是 Kondo 定理；low-ramification/basis alignment/naturality 是附加条件。
C5. p=12301 local Tate realization 只是局部 source；没有完整 global C 和全局 Galois image/权重。
C6. C9-ARCH 的 finite-vs-arch 数值比较继承 finite `h_A` 的条件性；arch 上界本身 paper-level、donor-independent，但 “补偿不足” 只能相对 conditional finite lower bound。
C7. `h_∞^actual` 仍缺；arch 只有 upper bound，不能给出 lower bound 或实际正补偿。

### 3.3 Invalid as written（作为 actual/target proof）

I1. C9-UNIFORM 的 “Branch A is actual (source-symplectic/aligned hull)” 作为**实际目标下界**不成立；C9-IND1-GLOBAL 已把 (11)–(14) 撤回。算术值仍是 arithmetic-valid。
I2. C9-UNIFORM 的 “zero-Kummer integer-domain bound already above Q_p” 作为 actual target claim invalid/conditional：它只是公式值高于 Q_p，不代表 actual output hull 含该 bound。
I3. C9-GLOBAL §6 “已证”清单中的 T7/T8/T14/T15、branch classification、target assembly：不能列为已证 actual；T7/T8 是 inferred，T14/T15 依赖 withdrawn target step。
I4. `F(Hull(...)) ⊂ H_C` 或由 F 为 ring iso 推出 target containment：invalid（task-149 §5.3）；还缺 TC-B/TC-C。
I5. b=3 B=I 的 `9/41` surplus 作为 actual：invalid/conditional；natural alignment 下 B=O_K，B=I unavailable（MODP）。
I6. C9-ARCH b=273 用 `−38736/41` 作 h_p：invalid label（B branch）；correct A value `−39156/41`。结论不变但数值不能照抄。
I7. 任何 L/Hull 的 “已证全局 h_C≥Q_C” 或 “已构造全局反例”：invalid；没有完整 C，没有 target containment，也没有 h_∞ lower bound。

## 4. Archimedean 上界审计

Paper-level（不依赖 symplectic donor）：

```
IV Prop1.5(iii)(iv): tensor of length≤π factors lies in π^{j+1}B_I;
IV Thm1.10(vii): log-volume(B_I)=0, so log-volume(π^{j+1}B_I)=(j+1)logπ;
after procession average over j=1..m, m=(l−1)/2:
A_arc(vQ) ≤ ((l+5)/4)logπ.
```

l=41: `(46/4)logπ≈13.164394` natural。TAME 表格单位是 log p，故对 p≥43：`≤3.500052` log p；对 p=12301：`≤1.397875` log p。

限制：

- 这是 **upper bound**，不是 actual archimedean image 的下界；`B_I` 只是 unit ball，不能把 upper bound 当作补偿存在。
- 与 finite deficit 比较时，finite 侧是 conditional；但若接受 conditional finite `h_A`，则 b=3 A deficit `408/41≈9.951` > 3.500，b=273 A deficit `38883/41≈948.366` > 3.500，uniform b=1347 A deficit `191928/41≈4681.171` > 3.500；arch-only 不足。ρ=1/2 的 b=1347 direct-domain bound 已在 Q_p 之上（gap 负），无需 arch；b=3 direct-domain 仍亏，但 finite 侧 conditional。
- arch 上界不补 `h_∞` 的实际 lower bound；C9-GLOBAL 的 (G10) 仍只能保留为未定符号。

## 5. 对 C9-IND1-GLOBAL / task-155 的逐项对应

| 被审计断言 | 状态 | 原因 |
|---|---|---|
| (11)–(14) target containment | withdrawn / conditional | task-149: full Ind1 is procession automorphism, needs TC-A..H/TC-S; ring iso alone insufficient |
| h_A aligned actual hull | conditional | depends on TAME §5 (11)–(14), withdrawn |
| h_B/B=I branch | conditional arithmetic; not actual | task-155: B=O_K under inferred alignment; B=I unavailable |
| G1/G6 global assembly | conditional | uses h_A/target containment; W2/W3 template inferred; h_∞ missing |
| b=3,273,1347 rational values | arithmetic-valid | exact recomputation §1 |
| arch bound | paper-level valid | IV Prop1.5/Thm1.10(vii), donor-independent |
| arch-only compensation conclusion | conditional | arch upper valid; finite side conditional; no actual h_∞ lower bound |

## 6. 最终 ledger

**Arithmetic-valid:** b=3,273,1347 的 uniform `Σs,h_A,h_B,Q,D`；ρ=1/2 b=3,1347 的 `h,h_direct,Q,gaps`；`T=1/2`；G4 恒等式；uniform A 分支永不闭合的代数证明；arch 上界数值换算；tame trace 表。

**Conditional:** `h_A` 作为 actual aligned target lower bound；`h_B`/B 分支；GLOBAL G1/G6/W2/W3；T7/T8/T14/T15 的实际来源；p=12301 本地 realization；arch-vs-finite 比较；完整 C 的全局权重/h_∞。

**Invalid as actual/target proof:** C9-UNIFORM “Branch A actual”；zero-Kummer bound as actual target；C9-GLOBAL “已证” target assembly；`F(Hull)⊂H_C` from ring iso；b=3 B=I surplus as actual；C9-ARCH b=273 B value as h_p；任何未构造完整 C 的全局 h_C≥Q_C/反例声明。

## 7. 版本身份与状态

本审计只做算术/依赖复核，不新增 local construction。P6 仍 open；target_accepted=false；没有 Lean/Project/kernel/comparator/独立审查。

精确计算的来源约定：uniform 的 `s_j=floor(bj²/41)`；ρ=1/2 的 `h` 按 TAME (15)/(15-u) 与 `h_direct=h−23/2`；所有分数用整数/有理数；没有浮点外推。

