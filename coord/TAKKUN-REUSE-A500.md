# TAKKUN 复用映射（A500）—— Θ 值 / 2ℓ 根 / log-shell 真实构造 ↔ 我们的 O2 对象

来源：`tmp/sheaf/takkun/IutLean/`（68 文件，移植入队；只采纳对象定义/已验证引理，
其结论作为待审计数据）。本节只写映射与可复用清单，不改任何源码。

## 1. 逐文件：真实构造与关键已验证引理

### `Theta/ThetaValues.lean`（namespace `IUT.Theta`）
- `gaussExp (j : ℤ) : ℤ := j^2`；`gaussExp_neg/zero/nonneg/succ_sub`（`e(j+1)-e(j)=2j+1`）。
- `thetaValue (q : M) (j : ℤ) : M := q ^ gaussExp j`（`CommGroup M`）；
  `thetaValue_zero`、`thetaValue_neg : θ(−j)=θ(j)`、`thetaValue_eq_of_eq_neg`、
  `thetaValue_div_zero : θ(q,j)/θ(q,0) = q^{j²}`。
- `thetaValueMon (q : M) (j : ℤ) := q ^ (gaussExp j).toNat`（Nat 指数版本，适用于幺半群）。
**O2 映射**：我们的 `qThetaValue` 就是 `thetaValueMon qroot j`（M = L_b 的乘法幺半群）；
`gaussExp` 与 `thetaValue_neg` 直接给出 `±1` 对称性；**可整文件复用定义与引理**。

### `Theta/ThetaGroup.lean`（`IsThetaGroup`）
- 类 `IsThetaGroup G`：所有交换子落在中心；`commutatorElement_mem_center`、
  `commutatorElement_mul_left/right`、`commutatorElement_center_mul_left/right`、
  `thetaPairing : G→G→center G`（`thetaPairing_coe/swap/inv/naturality/congr`）
  `commutator_le_center`，`CommGroup` 实例。
**O2/下游映射**：Ind2 的 `μ_{2ℓ}` 中心扩张与 Θ-link 的交换子配对 = `thetaPairing`；
可作为 O2 `ind2Images` 的群论骨架（我们的 ind2 用单位群乘法；可升级为 theta 群模型）。

### `Theta/MonoTheta.lean`（`MonoThetaEnvironment`）
- `ConstantMultipleRigidity`/`constantMultipleRigidity`（中心元不改变交换子）；
- `DiscreteRigidity`/`discreteRigidity`；`MonoThetaEnvironment`（`thetaCyclotome`、
  `unitCyclotome`、`cyclotomicRigidity`）、`synchronization` 与 `synchronization_equivariant`。
**O2/下游映射**：Θ-link 的单值化/`Λ(Θ)` 同步化；不进入 O2 结构本身，但可作为 O2 之后
Θ-link 对象的现成真实构造（比我们自建的单位乘法 Ind3 精确）。

### `Padic/PadicLog.lean`（`ℚ_[p]`）
- `logTerm`、`logOnePlus := ∑' n, logTerm x n`、`summable_logTerm`；
- `norm_logTerm_le`、`norm_logOnePlus`（`p≠2, ‖x‖≤1/p` ⇒ `‖log(1+x)‖=‖x‖`）、
  `logOnePlus_shell`（`log` 把 `pℤ_p` 映到 `pℤ_p` 且保范）。
**O2/下游映射**：log-shell 的 p-adic log 真实化；可支撑 O2 之后 log-shell/Θ 值半径计算；
注意 `p ≠ 2` 条件（与我们 `l ≥ 5` 相容）。

### `Padic/LogShellRadius.lean`
- `aRadius (p e)`、`bRadius (p e)`（IUT-IV Prop 1.2 的 `a_i/b_i`），
  `aRadius_tame = 1/e`、`bRadius_tame = -1/e`、`radius_tame`、`one_div_le_aRadius`、
  `le_aRadius`、`aRadius_lt`、`neg_one_div_le_bRadius`、`aRadius_one = 1`、`bRadius_one = -1`。
**O2 映射**：O2 `hull = s1902Hull`（最小 `λ·O`）的**半径常数**可用 `aRadius/bRadius` 表述；
这些是已验证的 IUT-IV 常数，不依赖 LANA。建议 O2 的 hull 半径字段/定理改用这些常数命名。

### `Padic/LogVolume.lean`
- `logVol (x : ℚ_[p]) := Real.log ‖x‖`；`logVol_one`；`logVol_mul`；
  `logVol_pow : logVol (x^n) = n·logVol x`；`logVol_p_pow`；`logVol_mono`；
  `logVol_logOnePlus`（log 保体积）；`logShell_vol_boundary`；
  `logShellVolFormula (p e f m) = -((1/e)+(m/(e f)))·log p`、`logShellVolFormula_unramified`、
  `logShell_vol_eq_formula`；`curve11a3_qShell_logVol`（11a3 Tate 参数真实算例）。
**O2 映射（关键）**：O2 的 Θ 读法 log-volume 可用 `logVol` 独立计算：
对 `qroot ≠ 0`，`logVol ((qroot)^{gaussExp j}) = gaussExp j · logVol qroot`（`logVol_pow`），
这正是**不定义式 q/(2ℓ)** 的独立 Θ 读法公式；`logShellVolFormula` 可直接给出 O2 hull 的
局部体积项（`e,f,m` 参数）。

### `Padic/ShellTransport.lean`
- `shell (lam : ℤ) : Set ℚ_[p] := {x | ‖x‖ ≤ p^{-lam}}`（`= p^lam ℤ_p`）；
  `mem_shell`、`shell_subset_iff : shell λ ⊆ shell μ ↔ μ ≤ λ`；`mul_mem_shell`；
  `shell_le_one`；`expQ_mem_shell`、`expQ_shell_surjective`、`expQ_shell_existsUnique`；
  `unit_mul_shell`（`‖c‖=1` 时 `c·S_λ = S_λ`）；`le_one_mul_shell`；
  `logVol_shell_gen : logVol (p^lam) = -lam·log p`。
**O2/下游映射**：Ind3 的单位乘法「保壳」真实引理 = `unit_mul_shell`；
O2 `ind3Images` 目前用根扩单位乘法，可直接复用此引理到 ℚ_p 局部模型；
`shell_subset_iff` 是 hull 的 `λ·O` 包含关系（Remark 3.9.5(i)）的现成序同构。

### `Arithmetic/RealKummer.lean`（2ℓ 根的真实根体系，重点）
- `realQRootSystem : RootSystem (M := (AlgebraicClosure ℚ_[p])ˣ) qParam`，
  由 `rootSystemOfAlgClosed`（`Cyclotome/Kummer.lean` 的**全阶乘相容根链**）给出；
  取 `n = 2ℓ` 即得真实 `qroot`（`qroot^{2ℓ}=q`）。
- `realThetaRootSystem (j) = realQRootSystem.pow (gaussExp j)`（`RootSystem.pow`），
  对应全 theta 值 `q^{j²}` 的相容根体系；`realQKummer`/`realThetaKummer` 及其 1-cocycle。
**O2 映射（重点）**：O2 的 `qroot` 应由 `rootSystemOfAlgClosed q` 的 `2ℓ` 层给出
（而不是只在 `L_b` 里取一个根）；`thetaValue` 用 `realThetaRootSystem` 的 `gaussExp` 次幂。
这样 O2 的 `qroot^(2ℓ)=q` 与 theta 值的 Kummer 类有真实构造基础。

## 2. O2 字段映射表（我们的 `Mzk1ThetaPilotObjectActual`）

| O2 字段 | 当前实现 | takkun 复用 | 动作 |
|---|---|---|---|
| `Vbad` | `Finset.univ : Bad(nativePlaceSelection T)` | takkun `CoreData`/`InitialThetaData` 的 bad 集（局部版） | 保留我们的 V_bad；参考其 cardinality/F_l 计数（`Fl.card_GeoSym`） |
| `qroot` | `rootNormedElement`（L_b 内） | `realQRootSystem`/`rootSystemOfAlgClosed`（ℚ̄_p 全根链，2ℓ 层） | **改用根体系构造**并证明 `qroot^(2ℓ)=q`；L_b 根作为其像 |
| `thetaValue j` | `qroot^(gaussExp j)` | `IUT.Theta.thetaValueMon qroot j`（同式） | 直接复用 `thetaValueMon`/`gaussExp`；用 `thetaValue_neg` 给 `±1` |
| `thetaValue_pow` | 手工 `pow_mul` | `IUT.Theta.thetaValue_div_zero` + `logVol_pow` | 以 takkun `thetaValue` 引理重写/复用 |
| `ind1Images` | `Equiv.Perm` 标签置换 | takkun `Combinatorics/Fl`（`LabCusp ≅ F_l^×/{±1}`, `GeoSym`） | 用 Fl 的 `±1` 商/Gauss 对称性替代任意置换模型 |
| `ind2Images` | `rootsOfUnity (2ℓ)` 乘法 | `Cyclotome/Frobenius` 的 `rootsOfUnity`/`FrobeniusCyclotome` + `ThetaGroup` 中心扩张 | 复用 μ_{2ℓ} 结构；用 `thetaPairing` 表达交换子中心 |
| `ind3Images` | 根扩单位乘法 | `Padic/ShellTransport.unit_mul_shell`、`PadicLog.logOnePlus_shell` | 用保壳/保范引理升级为真实 log-shell 单位作用 |
| `hull` | `s1902Hull`（root 乘积球） | `LogShellRadius.aRadius/bRadius` + `ShellTransport.shell` | 用 IUT-IV 常数/壳写 hull 半径与包含关系；保留 S1902 乘积球为 carrier 实现 |
| 读法体积 | `qThetaHullReadout=log‖q_V‖` | `Padic/LogVolume.logVol`/`logVol_pow`/`logShellVolFormula` | **独立**公式：`logVol(thetaValueMon qroot j)=gaussExp j·logVol qroot`，不出现 q/(2ℓ) 定义式 |

## 3. 可直接复用的引理清单（建议优先 import/引用）

1. `IUT.Theta.thetaValueMon`、`IUT.Theta.gaussExp`、`thetaValue_neg`、`thetaValue_div_zero`
   （`tmp.sheaf.takkun.IutLean.Theta.ThetaValues`）——O2 thetaValue/±1 对称性。
2. `rootSystemOfAlgClosed`、`RootSystem.pow`（`Cyclotome/Kummer.lean`）与
   `realQRootSystem`/`realThetaRootSystem`（`Arithmetic/RealKummer.lean`）——O2 qroot（2ℓ 层）
   与 theta 值根体系。
3. `IUT.Padic.logVol`、`logVol_pow`、`logVol_mul`、`logVol_shell_gen`、`logShellVolFormula`
   （`Padic/LogVolume.lean`）——O2/Θ 读法的独立解析公式与 hull 局部体积。
4. `IUT.Padic.shell`、`shell_subset_iff`、`unit_mul_shell`、`le_one_mul_shell`
   （`Padic/ShellTransport.lean`）——O2 ind3/hull 的保壳与 λ·O 序关系。
5. `aRadius`/`bRadius` 及其 tame/one 值（`Padic/LogShellRadius.lean`）——hull 半径常数（IUT-IV）。
6. `IsThetaGroup`/`thetaPairing`/`constantMultipleRigidity`/`discreteRigidity`
   （`Theta/ThetaGroup.lean`、`Theta/MonoTheta.lean`）——Ind2/Θ-link 的群论骨架；
   下游 Θ-link 优先用 `MonoThetaEnvironment.synchronization`。
7. `logOnePlus`/`norm_logOnePlus`/`logOnePlus_shell`（`Padic/PadicLog.lean`）——log-shell 半径的 p 进对数真实化（p≠2）。

## 4. 适配注意（与 O2 的差异）

- takkun 是**局部 ℚ_p / 代数闭 ℚ̄_p** 与抽象 `CommGroup M`；O2 是 `V_bad` 上的乘积（`S1902Carrier`）。
  局部引理需逐 `b` 施加（我们的 `qThetaValue` 已是逐 b 定义，结构相容）；全局量需再做 `∑ b`。
- takkun 的 `thetaValue q j` 中 `q` 是**已是 2ℓ 次根的 q_v**（`θ=q_v^{j²}`）；对应 O2：`q := qroot`，
  `qroot` 来自 `rootSystemOfAlgClosed q` 的 `2ℓ` 层。**不要**再把 theta 读法定义成 `log q /(2ℓ)`：
  独立读法应为 `logVol (thetaValueMon qroot j) = gaussExp j · logVol qroot`（j² 倍，不是常数 1/(2ℓ)）。
- `logVol` 在 `x=0`/`qroot=0` 需非零假设；O2 的 root 单位保证非零（`rootNormedUnit`/`Units`）。
- takkun 的结论（Hodge theater/Kummer cocycle 等）按 Lead 指示只作待审计数据；本节只把定义/已验证引理列为可复用。
