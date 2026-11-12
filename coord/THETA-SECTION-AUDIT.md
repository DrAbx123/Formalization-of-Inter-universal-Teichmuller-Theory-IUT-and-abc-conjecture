# THETA-SECTION-AUDIT — theta 乘积截面与 hcmp 方向审计（A1088）

日期：2026-11-13。**Status: READ-ONLY AUDIT；不编译、不新增 Lean。**
对象：`coord/THETA-SECTION-PLAN.md`；`tmp/sheaf/xif/paper/Mzk1ThetaSectionActual.lean`（SHA16 `B34D2758B4041CF9`，**ole=False**）。

## 0. 结论先行

1. **deg 符号自相矛盾**：Plan §1/§4 用 `deg = arch_bound - finite_index`（小 arch + finite 生成 ⇒ deg≤0），但 Plan §5 与 Lean `deg_eq` 写成 `degree = finite_index - arch_bound`，符号相反；因此 `hcmp_of_theta_section : degree≤0` 在给定字段下**不成立**（反例：`finite_index=1, arch_bound=0` 时 degree=1>0，而 `finite_ge/arch_le` 均满足）。
2. **arch/finite 估计**在 Lean 中是显式字段 `arch_le : arch_bound≤0`、`finite_ge : 0≤finite_index`，状态也标 GAP-ARCH-THETA/GAP-PVAL-THETA；**没有被当成证明**。但 `arch_bound/finite_index` 与 `section/theta` 无关，字段可任意取值，结构可空洞满足。
3. **theta 乘积截面没有真正编码**：`section_nonzero : Prop`、`section_eq_prod : Prop` 是任意 Prop，没有 u_j、没有 `section = ∏ θ_j^{j²}` 的等式，也没有 nonzero 的证明；Plan §5 甚至写 `section_eq_prod : True`。因此“对象存在性”不是有效 GAP，而是空模板。
4. **没有发现用 hcmp 证 arch 的循环**：arch/finite 是独立字段，`hcmp_of_theta_section` 只做 `deg_eq + arch_le + finite_ge` 的线性算术（若符号修正后）。但 Plan §3(b) 引用的 `S3050Unit_eq_log_norm_div` 被标“green”，实际 A1066 已发现该定理符号错、文件未编译；这是**stale/invalid citation**。

## 1. deg 符号与 hcmp 方向

### 1.1 Plan 的两套公式

* §1：`deg^(L) = (1/[K:Q]) ( Σ_arch log‖s‖ − Σ_fin log#(L_p/O_p s) )`；
  小 arch（`Σ_arch≤0`）+ 有限生成（`Σ_fin log#≥0`）⇒ `deg≤0`；
* §4 合成：`arch_bound≤0`、`finite_index≥0 ⇒ deg=arch_bound−finite_index≤0`；
* §5 Lean 草案却写 `deg_eq : degree = finite_index - arch_bound`；与 §1/§4 **相反**。

### 1.2 Lean 实际

```lean
arch_bound : Real; arch_le : arch_bound ≤ 0
finite_index : Real; finite_ge : 0 ≤ finite_index
deg_eq : degree = finite_index - arch_bound
theorem hcmp_of_theta_section (D) : D.degree ≤ 0 := by rw [D.deg_eq]; linarith [D.finite_ge, D.arch_le]
```
由 `finite_ge` 与 `arch_le` 只能得 `degree = finite_index - arch_bound ≥ 0`，不能得 `degree≤0`；
反例 `finite_index=1, arch_bound=0 ⇒ degree=1`。**该定理按现字段 INVALID**（即使不考虑编译）。

**修正**：若采用 Arakelov 约定 `deg=arch−finite`，则 `deg_eq : degree = arch_bound - finite_index`，
由 `arch_bound≤0`、`finite_index≥0` 得 `degree≤0`；此时 `hcmp_of_theta_section` 才是真算术。

### 1.3 与 StructuralLineBundle/Form C 的 hcmp 方向

* Plan `hcmp := deg(DetBundle)≤0`；StructuralLineBundle 的 `hcmp` 是 `globalLogVolume det≤globalLogVolume q`；
  两者之间没有定理连接 `degree` 与 `globalLogVolume det−globalLogVolume q`；
* 因此 Plan 的 hcmp 方向本身对（deg≤0），但**不是** StructuralLineBundle 的 `hcmp`；
  必须补 `degree = (globalLogVolume det − globalLogVolume q)/(2l)` 或等价 bridge；否则两个 hcmp 只是同名。
## 2. arch/finite 估计：是字段还是证明？

* 是**显式字段**：`arch_le`、`finite_ge`；文件 header 也标 GAP-ARCH-THETA / GAP-PVAL-THETA；
  这一点符合“估计作为假设而非证明”的要求；
* 但 `arch_bound`/`finite_index` 是自由 Real，**没有**与 `section`、`theta`、`Bundle` 的度量/指数连接；
  因此结构可以被任意数值空洞满足；所谓“存在性=GAP”并不准确——抽象结构可平凡居住；
* Plan §3(a) 列了 arch 解析输入（Fourier/Petersson/Fay），但 Lean 没有这些类型/函数；只是 Real 字段；
* Plan §3(b) 的有限位论证（ordp_qrootOf、tame、S1422 hchar）在 Lean 中完全没有体现；
  只留下 `finite_ge` 假设。因此 finite 估计不是“部分用现有 green 标量”，而是**纯假设字段**。

## 3. theta 乘积截面构造与循环性

### 3.1 构造是否编码

Lean 结构只有：
```lean
Bundle : Type
section : Bundle
section_nonzero : Prop
theta : Fin nC → Real
section_eq_prod : Prop
```
* `section_nonzero`/`section_eq_prod` 是**任意 Prop**，不是 `section ≠ []`、也不是 `section = ∏...`；
  它们可以为 True 或 False，结构不需要任何证明；
* 没有 `u_j`、没有 theta 点、没有 Deligne pairing/张量积、没有 `theta(u_j)` 到 `section` 的联系；
* Plan §5 本身就写 `section_eq_prod : True`（placeholder）；Lean 只是把 True 换成任意 Prop；
* 因此 **theta 乘积截面构造没有实现**；`ThetaSectionData` 是空抽象模板，不能称为“对象存在性=GAP”。

### 3.2 循环性

* `hcmp_of_theta_section` 只使用 `deg_eq`、`arch_le`、`finite_ge`；**没有使用 hcmp**，也没有用目标去证 arch/finite；
* 因此**没有循环**；不过若后续把 `arch_le`/`finite_ge` 用目标或 hcmp 推出，才会循环；当前文件没有；
* 但 `section_eq_prod : Prop` 可以被设成目标/任意命题，不提供约束；这是空洞性，不是循环。
## 4. 判定汇总

| 对象 | 判定 | 说明 |
|---|---|---|
| `THETA-SECTION-PLAN` | **PARTIAL（含 INVALID 符号）** | §1/§4 与 §5 的 deg 公式相反；arch/finite 明标 GAP 但 Lean 未编码；theta 构造仅草案；引用 S3050“green”过时 |
| `Mzk1ThetaSectionActual` | **INVALID as written** | `deg_eq` 符号反了，`hcmp_of_theta_section` 不成立；`section_nonzero/section_eq_prod` 是任意 Prop；无 olean |
| arch/finite 估计 | **显式字段（正确做法）** | 没有当成证明；但字段与 section/theta 脱钩，空洞可满足 |
| theta 乘积截面 | **未构造** | 无 u_j、无 product 等式、无非零证明；仅空模板 |
| 循环性 | **无 CIRCULAR** | 未用 hcmp 证 arch；字段独立；但空洞性严重 |

## 5. 修正建议

1. 统一 deg 约定：二选一，但全篇一致：
   * 若 `deg = (Σ_arch − Σ_fin)/[K:Q]`，则 `deg_eq : degree = arch_bound - finite_index`；
   * 若坚持 Lean 的 `degree = finite_index - arch_bound`，则 hcmp 应写成 `0≤degree`（或把 `arch_bound` 定义成负 arch 和）；
   * 当前 Plan/Lean 不一致，必须修 Lean 的 `deg_eq` 与 Plan §5，不能只改文。
2. 把 `section_nonzero : Prop` 改成 `section_nonzero : section ≠ default`（或具体非零证明字段）；
   把 `section_eq_prod : Prop` 改成真实等式（需要 `u_j`、`theta`、张量积/乘积的类型），或删除并标 GAP；
3. `arch_bound`/`finite_index` 必须由 `section`/theta 数据定义（或至少加 `arch_bound_eq`、`finite_index_eq` 联系），否则结构空洞；
   若暂时不定义，header 应写 **abstract template; not an object construction**，而非“对象存在性=GAP”。
4. 补 `degree` 与 `globalLogVolume det−globalLogVolume q` 的 bridge；否则 Plan 的 hcmp 与 StructuralLineBundle 的 hcmp 只是同名。
5. 修正 `S3050Unit_eq_log_norm_div` 的符号（A1066 已报正号错；正确应为 `-log‖x‖/(2l)`）后再引用；当前“green”引用无效。
6. 无 olean（ole=False）⇒ watchdog/mainline 结果前一律 PENDING-WATCHDOG，不得写 PROVED。