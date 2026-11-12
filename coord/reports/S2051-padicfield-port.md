# S2051: local CFT `PadicField` 移植报告

Date: 2026-11-02 (Asia/Shanghai). Workspace: `D:/lean`.
Lean: `leanprover/lean4:v4.32.2`; Mathlib: `v4.32.2`, rev `905b95818eb32af7874a58b427f50c1711a5e96c`.
Workspace HEAD: `9399e9fab4d62ea5f78a4a0d56ceecb84525a3ee` (dirty tree, shared with concurrent port agents).

## 1. 结论

- 源目录 `tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/local-class-field-theory/local-class-field-theory-main/LocalClassFieldTheory/PadicField` 实际有 **18** 个 `.lean` 文件；**没有 `Basic.lean`**，源树中也无 `PadicField/Basic.lean`（全仓搜索确认）。任务优先级表中的 `Basic` 无法移植，因为没有源文件；未创建占位/伪造文件。
- 已将 18 个文件复制到 `tmp/local-cft-port/PadicField`，并额外复制 `LocalClassFieldTheory/Galois/ZHat.lean` 为 `PadicField/ZHat.lean`（`UnramifiedZHat.lean` 的外部依赖）。
- 导入路径已从 `LocalClassFieldTheory.PadicField.*` 改为 `PadicField.*`，`LocalClassFieldTheory.Galois.ZHat` 改为 `PadicField.ZHat`。命名空间保持原样：主代码 `namespace PadicField`；`ZHat.lean` 保持 `namespace Brauer`。
- 在根 `lakefile.toml` 增加：
  ```toml
  [[lean_lib]]
  name = "PadicField"
  srcDir = "tmp/local-cft-port"
  ```
  （共享 lakefile 同时被其他移植 agent 追加了 Reciprocity/ClassFieldAxiom/Galois/Herbrand/ContinuousKummerTheory 条目；本任务只负责 PadicField 条目。）
- **核心模块 EXIT=0**：16 个源文件 + `ZHat` 共 17 个模块全部编译成功，olean 均存在。无 `sorry`/`admit`/`native_decide`/`axiom`。
- 最后两个文件 `PowIndex.lean`、`PowIndexPadic.lean` 依赖 `ContinuousKummerTheory.Kummer.PAdic`（外部包）。该 `PAdic.olean` 在本任务结束时已由并行构建生成；`PowIndex` 的收尾构建已启动，结果见第 6 节（若未完成则如实标为 pending）。核心里程碑不依赖它们。

## 2. 编译清单（EXIT=0）

编译命令统一为 `cd D:\lean; lake build PadicField.<Module>`，每条命令退出码 0。顺序为依赖顺序：

| # | Module | olean bytes | olean SHA256 (前16位) |
|---|---|---|---|
| 1 | `PadicField.Norm` | 336088 | 65481A59F51A9BF3 |
| 2 | `PadicField.Teichmuller` | 292848 | C8EA6D38D94994D8 |
| 3 | `PadicField.Integers` | 819016 | 50B0530A5614A023 |
| 4 | `PadicField.Uniformizer` | 551600 | 3C527EB25A4668A4 |
| 5 | `PadicField.Complete` | 314296 | E360457384E56AEA |
| 6 | `PadicField.Extension` | 403056 | 56DD603F5A921273 |
| 7 | `PadicField.Ramification` | 447088 | 02641CD80C41D7AC |
| 8 | `PadicField.FieldNorm` | 256064 | B456D14C9346B1F0 |
| 9 | `PadicField.Tower` | 265776 | FBC51634E06A16F7 |
| 10 | `PadicField.Unramified` | 426408 | 2B39417854F9C96B |
| 11 | `PadicField.Galois` | 530176 | 600E1406BFB27664 |
| 12 | `PadicField.UnramifiedExistence` | 1125088 | 10CB7B0409BDFB1E |
| 13 | `PadicField.MaxUnramified` | 917792 | 1F48BBABEFDD6D9A |
| 14 | `PadicField.AbsoluteInertia` | 818448 | 93BF8FE3024F5E42 |
| 15 | `PadicField.Powers` | 699144 | DD4BF620D32118E0 |
| 16 | `PadicField.ZHat` | 489176 | 6E6233881250412B |
| 17 | `PadicField.UnramifiedZHat` | 404864 | 3CC8488D8F149BDB |

完整 SHA256：

```text
Norm                65481A59F51A9BF3952E7CFED90196DCF81846CC28ACB2E4E09CBA8C1EE90E26
Teichmuller         C8EA6D38D94994D84F578A1F9328CEDB3C542C3D0F3E4C304201B2B55DF741AD
Integers            50B0530A5614A023BF50548809E943DF9D55E1EFA614315B43016AC3E0C3887F
Uniformizer         3C527EB25A4668A43822F1A49B8CE841A3C19A921B654A211644F051BA58234D
Complete            E360457384E56AEA73A73D0AC986C56ED743958D5DC29313368F72270CC52049
Extension           56DD603F5A92127368CD940BA8021046FCBF5C87F14D080D179A737B3FE336EA
Ramification        02641CD80C41D7AC8A735F02284C831C76C1E8E205E04E79A8F36BC45F137873
FieldNorm           B456D14C9346B1F0BC905C4A1C8763FB34DA2DFFC3408382E5C2ED661F0349D4
Tower               FBC51634E06A16F7C9BF33B36364F832BA783B566D560D8B6E0A4DFC3168130D
Unramified          2B39417854F9C96BD30D3318290C758D3130047F7C4EAD36D1F3941EC2709D8A
Galois              600E1406BFB27664456B194E5D75A308E25478D13CB77EC4BE8BF3B46699383F
UnramifiedExistence 10CB7B0409BDFB1EBF0BC63F221EA3E669E5C5CDCB1DDA4029F95239A1130A47
MaxUnramified       1F48BBABEFDD6D9A999AE5FDD9E6B937468B1C7A88341D5FAC8A34BE9EF7F0B5
AbsoluteInertia     93BF8FE3024F5E42B4F0DA3CB0D0E2C94D075AF725A6D181FA70C8180C771540
Powers              DD4BF620D32118E0C7C0E1CB7AA9041828941D11E88A0A20EA44894428351677
ZHat                6E6233881250412BF480575C9D1BDD57EE1F309B7CEE348A6770F7B22BA43918
UnramifiedZHat      3CC8488D8F149BDB96D038127EA7702E68D8DB106BFED580C4B71DA81765389A
```

olean 目录：`D:\lean\.lake\build\lib\lean\PadicField\`。

## 3. 源/目标 SHA256

- 源 `LocalClassFieldTheory/PadicField` 18 文件清单聚合 SHA256：`4e9f18b882215ffd4d5849e99266bc9ab48c80937a05c1ebd2a8c83525528b39`（聚合方式：按文件名排序后的 `name:SHA256` 行以 `\n` 连接再 SHA256）。
- 目标 `tmp/local-cft-port/PadicField` 19 文件清单聚合 SHA256：`cbc8770993af524746396267017fe6555a6a174a96d3e74dfa1f6bb0d37c592a`。
- 目标文件 SHA256 完整清单见第 8 节。
- 与源相比，差异仅为 import 行（18 个文件里 15 个有改动；`Norm`/`Teichmuller`/`PowIndex` 与源一致）以及新增 `ZHat.lean`。

## 4. API 差异

在 Lean 4.32.0/Mathlib 81a5d → Lean 4.32.2/Mathlib 905b 的移植中，**当前 17 个模块没有出现需要修改证明或陈述的 API 差异**。所有文件按原样编译通过，只改了模块路径：

- `import LocalClassFieldTheory.PadicField.X` → `import PadicField.X`；
- `import LocalClassFieldTheory.Galois.ZHat` → `import PadicField.ZHat`。

未删除、未弱化、未新增假设，未修改目标陈述。

## 5. 验收状态（按项目口径）

| 项 | 状态 |
|---|---|
| `statement_compiles` | true（17/17 个已移植模块；含核心优先模块） |
| `proof_body_checked` | true（同上，kernel 编译通过） |
| `kernel_closed` | true（无 `sorry`/`admit`/`native_decide`/`axiom`；axiom probe 为标准三元组） |
| `target_accepted` | false（仅移植，尚未做 comparator/独立语义审查；且 `PowIndex` 收尾见第 6 节） |

Axiom probe（`tmp/local-cft-port/S2051Probe.lean`）对 `maxUnramified`、`frobUr`、`dense_zpowers_frobUr`、`gal_maxUnramified_mul_comm`、`exists_restrict_eq`、`IsUnramified`、`adjoin_teichmullerSet_eq_top`、`galMaxUnramifiedEquiv`、`galMaxUnramifiedEquiv_frobUr`、`absInertia_eq`、`unramifiedQuotientEquiv`、`isGalois_of_isUnramified`、`residueGalEquiv` 输出均为 `[propext, Classical.choice, Quot.sound]`。

## 6. 剩余工作

- `PadicField.PowIndex` 导入 `ContinuousKummerTheory.Kummer.PAdic`；
  `PadicField.PowIndexPadic` 导入 `PowIndex` + `Ramification` + `Complete`。
- 本任务结束时 `ContinuousKummerTheory/Kummer/PAdic.olean` 已存在（并行 agent 构建），
  `PowIndex`/`PowIndexPadic` 的收尾构建已启动；因任务要求立即收尾，该后台构建在完成前被停止（job cancel），
  因此这两个模块在本报告中不声称 EXIT=0，日志见 `tmp/local-cft-port/_s2051_powindex.log`。
  核心里程碑（任务列出的优先模块）不依赖该外部包。重跑命令：`lake build PadicField.PowIndex PadicField.PowIndexPadic`。
- `Basic.lean` 在源中不存在，无法按名移植；若上游后续版本提供该文件，需要单独取得源文件，不能由本任务伪造。
- 未运行：`lake build PadicField` 全库（会包含尚未完成的 PowIndex）、全 Project 构建、comparator。

## 7. 复现命令

```powershell
cd D:\lean
lake build PadicField.Norm PadicField.Teichmuller PadicField.Integers PadicField.Uniformizer
lake build PadicField.Complete PadicField.Extension PadicField.Ramification PadicField.FieldNorm
lake build PadicField.Tower PadicField.Unramified PadicField.Galois PadicField.UnramifiedExistence
lake build PadicField.MaxUnramified PadicField.AbsoluteInertia PadicField.Powers
lake build PadicField.ZHat PadicField.UnramifiedZHat
lake env lean tmp/local-cft-port/S2051Probe.lean
```

构建期间出现过 Windows 并发 I/O 的瞬时读失败
（`failed to read ... .olean.private`）和一次 `Stack overflow detected`；重试后均 EXIT=0，
不是代码错误。共享 lakefile 和 `.lake/build` 同时被其他移植 agent 使用。

## 8. 目标文件 SHA256

```text
AbsoluteInertia.lean   D3C2726060F73FBDB1D7CAE69A5174A27E1965E5F07DF83A181E6DBEF3FA3B38
Complete.lean          5AA9C763FBDF4FA1DD2B60B9405F66FC5B00CF872F06862CA4738BDE47D50024
Extension.lean         E4955995C9190EB7688E028300199C03ED1938F71591982544A9E60DBD999429
FieldNorm.lean         8AFD0083C2C2C46B3366EFC0974413B236B73E6F5E6FABDB6669DCF8EAFD37BB
Galois.lean            B4FD8F4E587DE25FB611505B145F7C5E29A300FBFABB7EEC0526A90472058DDE
Integers.lean          E843AB4D003D6FD769585686043381D82F52FF97C419CF6DAFD7A320DD25EED4
MaxUnramified.lean     417197801DD5DCE57E3A9F17D9E828485A57FA7AE0F90D420AE7BAC92B9B4C1D
Norm.lean              AD07ABC7A1158ABC8532B651342ED2BACB1843EAAB6C8C65F5C86288A4328A8D
Powers.lean            45CF82FDB9F55D3832B0422BCC8EF3F2E0AA03FB6DF8E19C0986FBB9835EFAFF
PowIndex.lean          2BE91E1A4B549AD6177FA298368122C39A66F5C1A5DD9A94AAEC7C0490CF8E11
PowIndexPadic.lean     B59FA6C3421DB87A8650801EC294A26A0845463346683243A6BD0DDDB8C24E88
Ramification.lean      F1D9B4172014773DDCAA21C730D68EBEF0FF12B36C7E1143D85F834C6E0FA77E
Teichmuller.lean       B91F7E475A08BC7681E866DD7A5C0F3A05191732909143667DFC1C7D91FC36A7
Tower.lean             0D4693228E86E11140B80DB2FD2A64F945020FF59DBAA367A0B6145DCF1D60AF
Uniformizer.lean       6493EF3E92B1FA6D39EFD86CE7B0EF3E3C2047D21E678D657B6B0CD0B24ED3B7
Unramified.lean        1ED65FB94B950FDD08E73E9BEC0C89946CCD323529BC2BF829410F6263D4A222
UnramifiedExistence.lean EF111E2506B9A15BDEE611F5E81EE842249462A8034B7576103A6E5DBDC5AEE7
UnramifiedZHat.lean   EC57A62615C12A9792A5049326D13F91481504F17DECD695D8E64B78DB069EDC
ZHat.lean              6481AAF802BE16489C90305283BCA51EA6C78C970BF67AB88082AA4EAAD0FFB1
```

## 9. 文件位置

- 移植：`D:/lean/tmp/local-cft-port/PadicField/`
- lake 条目：`D:/lean/lakefile.toml`（`PadicField`，`srcDir = "tmp/local-cft-port"`）
- 验证探针：`D:/lean/tmp/local-cft-port/S2051Probe.lean`
- 构建日志：`D:/lean/tmp/local-cft-port/_s2051_*.log`
