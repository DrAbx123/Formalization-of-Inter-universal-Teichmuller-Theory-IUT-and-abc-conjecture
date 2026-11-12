# STAGE4-AUDIT-QUEUE-A932 — A2″/B1′/C0/E1-E4 待审计清单

日期：2026-11-12 19:11 起。**状态：AUDIT QUEUE（未审计；以下 hash/olean 为交接快照，不代替 stage4 复核）。**

口径：stage4 只审计下列文件；任何“条件接口”不得被写成“已证字典/已证 ABC”。所有路径相对工作区 `D:\lean`。

## 1. 审计对象与快照

| 文件 | size | src SHA256 | olean | 当前语义 | 优先级 |
|---|---:|---|---|---|---|
| `tmp/sheaf/xif/paper/Mzk1E4DictionaryActual.lean` | 2,619 | `A851D007A410EF108D9B32B0F05C8B74A0A68334C6E2980830084D84A86653C9` | 19:08:48 有 | E4 **接口**：`E4Dictionary`/iff/条件消费者；无 actual P/VolShell | P0 |
| `tmp/sheaf/xif/paper/Mzk1E1ConcreteActual.lean` | 3,918 | `0298633FF022292F77ADBF17B519D9E9B1560E6A6650D70A602CF19AD6E965F6` | 19:09:52 有 | E1 条件：`q.order=0 ⇒ qSide=0 ⇒ E1PaperScaledHull`；`l=5/{2}/{2,11}` 是 MODEL | P0 |
| `tmp/sheaf/xif/paper/Mzk1OurFrameworkABCActual.lean` | 2,642 | `8052B1EF16C81EE859BCD71AE2153171968F4BCECA558C23C86370E2DEF2604C` | 19:09:22 有 | 条件装配：`OurFrameworkAssumptions`；最终只消费 E3；**不证明 ABC** | P0 |
| `tmp/sheaf/xif/paper/Mzk1C0TargetsActual.lean` | 5,872 | `2D1649F1FF81487696A10C8292E77676A32CF3247AB1F3CC32390612A5B13F45` | 18:56:28 有 | C0 条件 T1/T1′/T2；缺口 `TensorAutCommutationDefect`/`TensorMetricOrthogonality`/exact hull formula | P1 |
| `tmp/sheaf/xif/paper/Mzk1BCertificateFullActual.lean` | 2,856 | `2D20DA0E7AC9192018178B3F8F54FB996CBFBDB5630C6D4F34E3B65B6E4D611A` | 19:01:23 有 | rank 2 certificate（B 线） | P2 |
| `tmp/sheaf/xif/paper/Mzk1BCertificateGeneralActual.lean` | 2,696 | `ED2BEF73A76F333CC4B1BE6B714BB8B400466A9D02DC1381E1B0C0CB709D6EB7` | 19:09:47 有 | rank 3 certificate（B 线） | P2 |
| `coord/b1_certificates.csv` | 60,092 | `DA5F9FE23BCB24EEE97C0B996C5BF70FC86CF8A151CEBCA251C1CA583B7565D8` | — | B1/B1′ certificate data；**data-only** | P2 |
| `coord/b1_certificates.json` | 239,266 | `8BC9D642A645DF64F707165D411D6F16E6FA66CCA641D28E5FBE4F1983C0B126` | — | 同上 | P2 |

**不列入审计**：`Mzk1E1ConcreteRealActual.lean` 草案当前**未落盘**（此前 19:11 出现过、随后不存在）；若 stage4 收到该文件需重新给 hash/oleans，不能沿用旧名。

## 2. 共通审计检查（每个 Lean 文件都要做）

1. **源码 pin**：`Get-FileHash <file> -Algorithm SHA256` 与上表一致；不一致 -> 以当前源码重新登记，禁止混用旧 olean。
2. **olean 新鲜度**：oleans 路径 `.lake/build/lib/lean/tmp/sheaf/xif/paper/<Name>.olean`；olean mtime > src mtime；否则重编译并记录 EXIT。
3. **独立编译**：`lake env lean tmp/sheaf/xif/paper/<Name>.lean`；记录 EXIT、输出行数、是否有 `sorry`/`warning`。
4. **公理/占位检查**：对每个 `#print axioms` 目标检查只有允许的 `propext`/`Classical.choice`/`Quot.sound`；零 `sorryAx`；不得有未声明 axiom/opaque。
5. **语义检查**：逐条读声明，确认没有把 **条件字段** 写成“已证”；确认没有把 MODEL/concrete datum 写成 actual 对象。
6. **import 闭包**：E1/E4/C0 targets/ABC 文件不得引入 lana `Iut/`（只允许 Mathlib/LeanFormal green）；如引入，标为“依赖 lana、不可 citable”。

## 3. 逐文件审计点

### 3.1 `Mzk1E4DictionaryActual.lean`（P0）

- 期望声明：`RegionLe`、`E4Dictionary`、`E4Dictionary_iff`、`e4_inequality`、`e4_of_unconditional`、`E4Witness`、`e4Rows_length=6`。
- 必查：`E4Dictionary` 的 `RegionLe R P → (sF−1)A ≤ VolShell` 是否只是命题定义；`e4_inequality` 是否只从假设 `hE4` 取结论；`E4Witness` 是否要求同时给 containment + volume_ineq（不能自动 inhabit）。
- 结论上限：**接口可 citable；E4 字典仍 GAP**。不得写成“E4 已构造/字典已证”。

### 3.2 `Mzk1E1ConcreteActual.lean`（P0）

- 期望：`qSideContribution_eq_zero_of_order_zero`、`E1PaperScaledHull_of_order_zero`、`ConcreteDatum`、`concreteQSide`、`concreteQSide_eq_zero`、`qSide_l5_two_zero`、`qSide_l5_two_eleven_zero`、`e1Rows_length=6`。
- 必查：`E1PaperScaledHull_iff_qSide_zero` 是否来自既有 green 文件；`qSideContribution` 定义是否使用 actual q-order；`ConcreteDatum` 的 `qOrder_zero` 是**字段**而非证明 actual order=0；l=5 两个 datum 的 `base=2` 是否与 MODEL 说明一致。
- 结论上限：**order-zero 蕴含 green；actual P 未构造、l=5 数据是 MODEL**；E1 仍条件接口。

### 3.3 `Mzk1OurFrameworkABCActual.lean`（P0，更新版）

- 期望：`OurFrameworkAssumptions`（E1_normalization/E2_volume_upper/E4_dictionary/E3_interface）、`ourFramework_ABCConjecture`、`ourFramework_E1`、`assumptionInterfaceRows_length=5`。
- 必查：`ourFramework_ABCConjecture` 是否**只消费** `A.E3_interface` 与 `classicalABCNatShape_iff_ABCConjecture`；E1/E2/E4 是否只是字段（E1 另被 `ourFramework_E1` 用）；确认没有 hidden axiom/sorry；确认 E3 字段类型仍是 `ClassicalABCNatShape`（等价 ABC，不是已证）。
- 结论上限：**条件装配；不是 ABC 证明**；stage4 只能登记“E1-E4 接口 wiring”，不能给 ABC 结果。

### 3.4 `Mzk1C0TargetsActual.lean`（P1）

- 期望：`ind2Term_eq_scaling_add_defect`、`ind2Term_frac_form`、`archDefect_eq_formula`、`TensorMetricOrthogonality`、`TensorAutCommutationDefect`、`c0TargetRows`。
- 必查：T1/T1′/T2 是否都是**纯算术**（输入 `hdef/hθ/hscaled/horth` 都是显式假设）；`TensorMetricOrthogonality` 与 `TensorAutCommutationDefect` 是否只是 `def ... : Prop`（未证明）；`c0TargetRows` 中 `GAP (lana)` 行不得被 stage4 当 green。
- 结论上限：**C0 条件目标 green；C0 精确化仍 GAP**；与 `coord/C0-EXACT-DERIVATION.md` 的源级缺口一致。

### 3.5 B1/B1′ certificates（P2）

- `Mzk1BCertificateFullActual`：rank2 证书（`rfRankTwo=5`, `rankTwo_certificate`, `rankTwo_five_dvd`），仅 rank 2 特例。
- `Mzk1BCertificateGeneralActual`：rank3 三坐标证书；仅有限秩小例。
- `b1_certificates.csv/json`：**data-only**，不构成 Lean 证明；stage4 只核对列/行数/生成脚本/50 样本与 941 全量口径是否一致。
- 结论上限：rank2/rank3 green；一般有限秩仍 GAP（缺 `Submodule.index`/Smith 标准形），B1′ 小样本 50%/0/25 已 STOP。

## 4. 阻断条件（stage4 必须打回）

1. 源码 SHA/olean mtime 不匹配，或 olean 不是从当前源码重编；
2. 任一目标含 `sorryAx`/未声明 axiom，或 `#print axioms` 超出允许集合；
3. E4/E1/C0 文件把条件字段/接口声明当成“已证字典/已证公式”；
4. ABC 文件被写成“ABC 已证”或 E3 之外字段被当作已消费的证明；
5. B1′/A2″ 的 STOP 结果被事后调参/改判据，或把 50% 写成 ≥80%；
6. 引用 `Mzk1E1ConcreteRealActual`（当前未落盘）或任何无 hash 的旧文件。

## 5. stage4 交付格式

逐文件一行：`name | src_sha | olean_fresh | EXIT | decls | axioms | sorryAx | semantic_verdict | citable?`；最后给：可 citable 列表、GAP 列表、需重编列表、被拒绝的语义声明列表。

## 6. A933 更新（stage4 审计后，lattice 复核）

- stage4 结果 `coord/STAGE4-AUDIT-RESULT-A932.md` 的快照为 **旧 ABC 版本**：`Mzk1OurFrameworkABCActual.lean` 当时 hash `8052B1EF…`、2,642B。
- 当前 ABC 版本（19:18:36）已是 **`9A4B9B11E44D5C526EF3F3216332FAD344B5424890481EC3CA56773CB0F73E83`**、4,274B，olean 19:19:31（fresh）。相对旧版：
  - `E2` 从空 Prop 改为 `E2VolumeUpper V logd logf C0 l := V ≤ ((l+5)/4)*logdf logd logf + C0`，并由 `ourFramework_E2` 消费；
  - `E4` 增加 `E4Dictionary`（来自 `Mzk1E4DictionaryActual`）与 `E4_face5`，`ourFramework_E4` 消费 `E4_dictionary`；
  - 声明数 4 -> 6（含 `E2VolumeUpper`、`ourFramework_E2`、`ourFramework_E4`）。
  - `E4_face5` 仍是未消费的额外字段；建议删除或补 bridge（不阻断）。
- **transitive lana 口径**：`Mzk1E1ConcreteActual`/`Mzk1OurFrameworkABCActual` 的 import 闭包经既有 green 栈到 `Iut.Foundations.Frobenioid`。**严格 lana-free 口径下标 `lana-transitive`，不作为 lana-free citable 证据**；只在“条件接口/wiring”口径下可引用，且不得用它们支撑任何 lana 事实。E4/C0 闭包纯 Mathlib，lana-free。
- 建议 stage4：对当前 ABC hash 重审 delta；在 EVIDENCE-ISOLATION §8 记录 `lana-transitive` 两个文件 + 当前 hash，并保留旧快照结果作历史。

## 7. A938 修复记录（lattice 执行）

- 当前 HEAD 修复前：`983A95B0…`/5,238B/19:25:55，独立 `lake env lean` **EXIT=1**；两个错误：
  1. `ourFramework_E1_of_qSide_zero` 里 `unfold Mzk1E1OrderActual.E1AllocationForm at h` 对带显式参数的 def 失败；改为 typed `have h : A.V_norm = A.V_hull + A.E1_qSide := A.E1_allocation`，`rw [hq, add_zero] at h`，`exact h`。
  2. `assumptionInterfaceRows : List (String × String)` 中放了 3-tuple；改为 `List (String × String × String)` 并给所有 8 行补第三项。
- 另外删除未消费的 `E4_face5 : Face5ConstructionObligation` 及 `Mzk1Face5ProofActual` import/open，消除 stage4 备注 2 的未消费字段；E4 只保留 `E4Dictionary`。
- 修复后：`lake env lean tmp/sheaf/xif/paper/Mzk1OurFrameworkABCActual.lean` **EXIT=0**；src SHA `4E7BAF5AF3272752D51BE3658B4AE8248E6372C04D6EECDFD83EF07757DCD6DA`，5,457B，19:34:36；olean 234,760B，19:35:02（fresh）。
- `tmp/a938_probe.lean`：`ourFramework_ABCConjecture/E1/E1_allocation/E1_of_qSide_zero/E2/E4` 全部 trio，`assumptionInterfaceRows_length` 无公理；EXIT=0，零 sorryAx。
- 语义不变：ABC 仍只消费 E3、条件于 E1/E2/E4；**不是 ABC 证明**。`lana-transitive` 标签保留（直接 import 无 lana，闭包经既有 green 栈到 `Iut.Foundations.Frobenioid`）。
- 待 stage4 对 hash `4E7BAF5A…` 作 delta 复审。

## 8. A941 定版（stage4 A940 REJECT 后）

- `4E7BAF5A…` **不得登记 green**：源码 L92-94 残留 `ourFramework_E4_face5` 定理（字段已删、`Face5ConstructionObligation` 未 import）；该源码不能编译，且当时 olean 不是该源码编出的。
- 已删除残留定理及 docstring；源码中 `E4_face5`/`Face5ConstructionObligation` 引用数 = **0**。
- 重编命令：`lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1OurFrameworkABCActual.olean tmp/sheaf/xif/paper/Mzk1OurFrameworkABCActual.lean`，**EXIT=0**。
- **定版**：src size 5,246B，mtime `2026-11-12T19:39:09`，src SHA `5AA68ED7F613838112FFE642D9476A5A6039D21FEF9CFAEBFAEB1254C0725BED`；olean size 234,760B，mtime `2026-11-12T19:41:12`（fresh）。
- `tmp/a938_probe.lean`：`ourFramework_ABCConjecture/E1/E1_allocation/E1_of_qSide_zero/E2/E4` 全部 trio，`assumptionInterfaceRows_length` 无公理；**probe EXIT=0**，零 sorryAx。
- 语义不变：ABC 仅消费 E3，条件于 E1/E2/E4；E2/E4 由 `ourFramework_E2/E4` 消费；`lana-transitive` 标签保留；不是 ABC 证明。
- **不再编辑该文件**；stage4 按此 hash 复审。

## 9. A942 stage4 复审结果：PASS（定版）

- stage4 复核 `5AA68ED7…`：SHA 一致（5,246B，src 19:39:09）；olean 234,760B@19:41:12 **fresh**；独立 `lake env lean` **EXIT=0**（0 errors/warnings）；`E4_face5`/`Face5`/`Face5Proof` 引用 = 0。
- probe：`ourFramework_E4_face5` unknown（olean 确由最终源码编出）；`ABCConjecture/E1/E1_allocation/E1_of_qSide_zero/E2/E4` 六声明 trio；`rows_length` 无公理；零 sorryAx。
- 语义确认：E2/E4 消费；ABC 仅消费 E3；非 ABC 证明；`lana-transitive` 保留。
- 登记：`EVIDENCE-ISOLATION §12` / `STAGE4-AUDIT-RESULT-A932 §9`；A941 CompletionUnconditional（lana-transitive）与 A943 E1 局部反例（lana-free，非完整 SourceDefinition31Data 反例）也已审计通过并登记。
- **该文件不再编辑**；此 pin 为最终审计依据。
