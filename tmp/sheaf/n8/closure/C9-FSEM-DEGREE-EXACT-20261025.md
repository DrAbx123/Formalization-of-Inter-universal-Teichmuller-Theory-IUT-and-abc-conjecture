# C9：F_sem/F 的 exact degree 与 field intersections

任务：task-234（exact global F_sem/F degree and intersections）。owner：iplsheapt。日期：2026-10-25。stage1 精确数域/局部域计算；无 U/B normalization；无 arbitrary data；无 Lean/Project edits；只写本文件。

输入：E_j from C9-CONSTRUCT-KCK / C9-EJ-COMPLETION / C9-DPRIMES-KODAIRA / C9-23-KODAIRA。

```
E_j: y²=x³−3j0/(j0−1728)x−2j0/(j0−1728),  j0=1/p^6,  p=12301,
D=1−1728p^6=−1009·50833·1799579·64860221162029,
F_sem = semistabilization compositum;  F=Q(i,E[6],F_sem).
```

状态：没有 Lean/Project/kernel/comparator/独立审查；P6 open；target_accepted=false。

## 0. 结果摘要

1. D-part：四个 local quartic fields 的 global Galois closures 都是

   `M_q = Q(i, q^{1/4})`, `[M_q:Q]=8`;

   pairwise intersection `M_q∩M_{q'}=Q(i)`；compositum

   `F_D=Q(i, q_1^{1/4},...,q_4^{1/4})`,  `[F_D:Q]=512`,  `F_D∩Q(i)=Q(i)`.

2. p=3 I0*：local quadratic semistabilization。`√3` 与 `√−3` 两个 ramified quadratic twists 都能 semistabilize（见 §3）；degree2。但 `E[6]` 含 `μ3=Q(√−3)`，`F=Q(i,E[6],...)` 含 `i`，故同时含 `√3=i√−3`；因此 p=3 quadratic **已被 Q(i,E[6]) 吸收**，对 `[F:Q]` 不增加 degree。
3. `[F_sem:Q]=1024`：D-part 512 乘 p=3 quadratic 2；后者与 F_D 交 Q（§4）。p=2、p=12301 无 semistabilization。
4. `F=Q(i,E[6],F_sem)=Q(E[6],F_D)`（因为 `i∈F_D`，p=3 K3⊂Q(i,E[6])）。令 `F0=Q(i,E[6])`，则

   `[F:Q] = 512·[F0:Q] / [F0∩F_D:Q]`.

   `[F0:Q] | 2·288 = 576`. Exact `[F0:Q]` 和 `F0∩F_D` 仍未算；故 `[F:Q]` 是 **conditional formula**，不是 exact numeric。若 `F0∩F_D=Q(i)`，则 `[F:Q]=256·[F0:Q]`；若 D-part 已在 F0 中，则 `[F:Q]=[F0:Q]`。见 §5。

## 1. D-part 局部/全局 field

对 q∈{1009,50833,1799579,64860221162029}，task-206 给出 local type III*、local semistabilization degree4。其 local model 在 `π'^4=q` 后 good（scaling `u=π'^3`），故 local semistabilization field 是

```
K_q = Q_q(q^{1/4}),   [K_q:Q_q]=4.
```

Global（Galois closure）：

```
L_q=Q(q^{1/4});   M_q=Q(i,q^{1/4});   [L_q:Q]=4, [M_q:Q]=8.
```

- `i∉L_q`：`L_q` 有一个 real embedding（q>0 的 real fourth root），而含 i 的域没有 real embedding；故 `M_q/L_q` 是二次，`[M_q:Q]=8`。
- 对 q≡1 mod4，`Q_q` 含 μ4，local `K_q/Q_q` cyclic quartic；q=1799579≡3 mod4 时 local extension non-Galois，其 Galois closure degree8。global `M_q` 总是 degree8。

### 1.1 Pairwise intersections

对 q≠q'：

```
M_q ∩ M_q' = Q(i).
```

理由：over Q(i)，`M_q=Q(i)(q^{1/4})` 是 Kummer 4-extension；Kummer classes `q,q'` 在 `Q(i)^×/(Q(i)^×)^4` 中独立。若 `∏ q_i^{e_i}` 是 Q(i) 中 fourth power，取 q_i-adic valuation 得 `4|e_i`，故 e_i=0。所以 compositum degree 是相对 degree 的乘积。

### 1.2 D-part degree

```
F_D := Q(i, q_1^{1/4}, ..., q_4^{1/4});
[F_D:Q(i)] = 4^4 = 256;  [F_D:Q] = 2·256 = 512.
```

这是 exact（Kummer independence above）。

## 2. p=2 与 p=12301

- p=2：E_j 的 minimal model good（task-229）；semistabilization degree1，无 field。
- p=12301：multiplicative I1，stable；degree1，无 field。

## 3. p=3：I0* 的 quadratic semistabilization

task-229：p=3 type I0*，degree2。显式地，若把 E_j 写成 quadratic twist

```
E = E0^{(d)}:  y²=x³+d²A0 x+d³B0,
```

则 `d=3` 与 `d=-3` 都使 inverse twist E0 在 Q_3 有 good reduction（Tate algorithm 检验 `val_disc(E0)=0`）。因此有两个可用的 ramified quadratic 解 twist fields

```
K3 ∈ { Q_3(√3),  Q_3(√−3) }   (both degree2).
```

这说明局部 semistabilization field **不唯一**，但 degree 固定为2；两个 choice 对下面 degree 无影响。

## 4. p=3 quadratic 与 D-part/Q(i) 的交

- `K3∩Q(i)=Q`：`Q(√3)` real；`Q(√−3)` 与 Q(i) 是不同 imaginary quadratic fields。
- `K3∩F_D=Q`：F_D 的 quadratic subfields over Q 由 Q(i), Q(√q_i), Q(√−q_i)（以及 possible products）生成，而 `√3`/`√−3` 对应 Kummer class 3/−3；q_i 都不是3，valuation 检查无 relation。
- 因此 `F_sem=F_D·K3` 的 degree：

```
[F_sem:Q] = [F_D:Q]·[K3:Q] = 512·2 = 1024.
```

这是 **exact**（给定 F_sem 包含 quadratic semistabilization；两种 K3 choice 都给1024）。

## 5. F=Q(i,E[6],F_sem) 的 degree

因为 `i∈F_D`，且 p=3 的两个 quadratic 都在 `Q(i,E[6])` 中：

```
E[6] contains μ3=Q(√−3) (Weil pairing on full E[3]);
F0=Q(i,E[6]) contains √−3 and i, hence √3=i√−3;
so K3 ⊂ F0.
```

因此

```
F = Q(E[6], F_D),   F0=Q(i,E[6]);
[F:Q] = [F0:Q]·[F_D:Q] / [F0∩F_D:Q]
       = 512·[F0:Q] / [F0∩F_D:Q].
```

已知：

```
[F0:Q] | 2·288 = 576   (E[6] image order divides |GL2(Z/6)|=288; i adds at most2);
F0 ⊇ Q(i),  F_D ⊇ Q(i);  so F0∩F_D ⊇ Q(i).
```

精确 degree 需要 `[F0:Q]` 与 `F0∩F_D`；当前没有 exact computation：

- `E[6]` 的 splitting field degree 可能小于288（取决于 mod2/3 image），未算；
- `F_D` 是否已经在 F0 中，未决。local 上 E 在 q 处 type III*，semistabilization quartic 可能被 6-torsion local field 部分/全部看到；这决定 `F0∩F_D` 是 Q(i) 还是更大。

### 5.1 条件性公式/端点

```
If F0∩F_D = Q(i):        [F:Q] = 256·[F0:Q]  (≤147456 if [F0]=576);
If F_D ⊂ F0:              [F:Q] = [F0:Q]     (≤576);
Intermediate intersection: 512·[F0]/[intersection].
```

因此 `[F:Q]` 目前只能给 **conditional formula**，不能给 exact integer；`[F_sem:Q]=1024` 是 exact。

## 6. exact / conditional / missing

### Exact

- D local type III*, local semistab degree4; M_q degree8;
- M_q∩M_{q'}=Q(i); F_D degree512;
- p=3 I0* degree2; two twist fields Q(√3),Q(√−3); K3∩F_D=Q;
- [F_sem:Q]=1024;
- K3⊂F0=Q(i,E[6]); F=Q(E[6],F_D); formula `[F:Q]=512[F0]/[F0∩F_D]`; [F0]|576.

### Conditional / missing

- Exact `[F0:Q]`（E[6] image order）和 `F0∩F_D`；
- 是否 F_D⊂F0（local inertia/6-torsion 的精确 image）；
- 显式 E[6] splitting field/division polynomial；
- 完整 C 的其他条件（mod41 image、C_K/V/ε、target）；
- 无 U/B normalization 依赖；无 arbitrary data。

## 7. 结论

```
D-part:  F_D=Q(i,q_i^{1/4}), [F_D:Q]=512, pairwise intersections Q(i).
p=3:    I0* quadratic; [K3:Q]=2; K3∩F_D=Q.
F_sem:  [F_sem:Q]=1024 (exact, up to choice of √3 vs √−3).
F:      F=Q(E[6],F_D); [F:Q]=512·[F0:Q]/[F0∩F_D], F0=Q(i,E[6]), [F0]|576.
Exact [F:Q] remains conditional on [F0] and F0∩F_D.
```

没有 U/B normalization；没有 Lean/Project edits；P6 open。

