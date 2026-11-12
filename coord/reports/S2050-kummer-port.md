# S2050: continuous-kummer-theory 移植报告（第一里程碑，提前收束）

日期：2026-11-02。工作目录 `D:\lean`（Lean 4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c）。

## 1. 交付位置

- Port 工作树：`D:\lean\tmp\local-cft-port\continuous-kummer-theory`（19 个 Lean 文件，与源 repo 逐字节一致，**零源码改动**）。
- 已调整：
  - `lean-toolchain` → `leanprover/lean4:v4.32.2`；
  - `lakefile.toml` → mathlib `v4.32.2`，lib 名 `ContinuousKummerTheory`，并记录移植编译命令。
- 未改 import：包内 import `ContinuousKummerTheory.*` 在 `-R <port根>` 下模块名一致，无需改写；namespace `KummerTheory`/`ContH1` 与工程现有 `Iut`/`LeanFormal` 无冲突（工程内无同名 namespace）。
- **无 fake / axiom / sorry 引入，未修改任何源文件的声明或证明。**

## 2. 编译命令（本树逐文件）

```powershell
cd D:\lean
$root='D:\lean\tmp\local-cft-port\continuous-kummer-theory'
$env:LEAN_PATH=$root
lake env lean -R $root -o $root\<Module>.olean $root\<Module>.lean   # 记 EXIT
```

两个必要修正（相对任务书里的 `-R D:\lean`）：

1. **必须显式 `-o`**：本工具链 `lean` 默认不写 olean（实测无 `-o` 时 EXIT=0 但无产物）。
2. **`-R` 用 port 根，而非 `D:\lean`**：port 路径含连字符（`local-cft-port`、`continuous-kummer-theory`），以 `D:\lean` 为根会得到含 `-` 的非法模块名；以 port 根为 `-R` 时模块名恰为 `ContinuousKummerTheory.*`，与 import 完全一致（已在 `tmp\_s2050probe2` 上验证 `-R`/`-o`/LEAN_PATH 语义）。
3. `lake env` 把工程 LEAN_PATH 放在前面、外部 `LEAN_PATH` 追加在末尾；因此工程 `.lake/build/lib/lean` 中已存在的同模块 olean 会被优先使用（见 §4 说明）。

## 3. 逐文件状态（SHA256 前 16 位）

| # | file | sha256(16) | 本树 EXIT | olean bytes | 位置 |
|---|---|---|---|---|---|
| 1 | `ContinuousKummerTheory.lean` | `d8afcde4bda49f5b` | root: 18 imports | — | — |
| 2 | `ContinuousKummerTheory/Hilbert90.lean` | `b6b1f5287974c722` | EXIT=0 (136.2s) | 337,032 | port tree |
| 3 | `ContinuousKummerTheory/ContH1/Basic.lean` | `fe2f0c1cbd52bdf2` | EXIT=0 once (133.4s); artifact later cleaned by rerun | 631,504 (lake) | project lake lib (byte-identical src) |
| 4 | `ContinuousKummerTheory/ContH1/Comparison.lean` | `d0c9e79a2d332e7c` | EXIT=0 (170.2s) | 1,427,912 | port tree |
| 5 | `ContinuousKummerTheory/ContH1/Corestriction.lean` | `de04854900d1e3dd` | olean present (lake build) | 408,144 | project lake lib |
| 6 | `ContinuousKummerTheory/ContH1/CorestrictionIndep.lean` | `53d65a27bec14642` | olean present (lake build) | 393,824 | project lake lib |
| 7 | `ContinuousKummerTheory/Kummer/Basic.lean` | `de5d5985f7fa6155` | olean present (lake build) | 611,304 | project lake lib |
| 8 | `ContinuousKummerTheory/Kummer/Equiv.lean` | `a46e03d370e1f088` | olean present (lake build) | 317,032 | project lake lib |
| 9 | `ContinuousKummerTheory/Kummer/Restriction.lean` | `8ec123c8622ff158` | olean present (lake build) | 532,184 | project lake lib |
| 10 | `ContinuousKummerTheory/Kummer/Corestriction.lean` | `251ca3505ce7319e` | olean present (lake build) | 617,752 | project lake lib |
| 11 | `ContinuousKummerTheory/Kummer/CorRes.lean` | `75ec0673acee83ab` | olean present (lake build) | 138,624 | project lake lib |
| 12 | `ContinuousKummerTheory/Kummer/Values.lean` | `9a0c3b540083e18d` | olean present (lake build) | 235,080 | project lake lib |
| 13 | `ContinuousKummerTheory/Kummer/Specialization.lean` | `07144cf477d65394` | olean present (lake build) | 1,146,088 | project lake lib |
| 14 | `ContinuousKummerTheory/Kummer/Decomposition.lean` | `63774e172bbeda72` | olean present (lake build) | 500,792 | project lake lib |
| 15 | `ContinuousKummerTheory/Kummer/Limit.lean` | `da9e92e3a13d5bf0` | olean present (lake build) | 1,029,160 | project lake lib |
| 16 | `ContinuousKummerTheory/Kummer/ZHat.lean` | `be2082c8c57997e0` | olean present (lake build) | 814,216 | project lake lib |
| 17 | `ContinuousKummerTheory/Kummer/ProfiniteCompletion.lean` | `cc3b82d654b2d325` | olean present (lake build) | 375,800 | project lake lib |
| 18 | `ContinuousKummerTheory/Kummer/Topology.lean` | `2a099d4ab009f91b` | olean present (lake build) | 460,912 | project lake lib |
| 19 | `ContinuousKummerTheory/Kummer/PAdic.lean` | `474b8a2df407747b` | olean present (lake build) | 770,360 | project lake lib |

小计：**本树实测 EXIT=0 且 olean 留存 2/19**（Hilbert90、ContH1.Comparison）；ContH1.Basic 曾 EXIT=0（133.4 s）但产物被后续重编清理；其余 16 个模块在**工程 lake 库**中已有成功产物（见 §4），但本树逐文件重跑尚未全部完成。

## 4. 关键发现：无 API 差异；阻塞来自并发环境的瞬时读错误

1. **Mathlib 905b958 下未发现任何 API 不兼容。** 工程 `lakefile.toml` 已被并行 worker 注册
   `[[lean_lib]] name = "ContinuousKummerTheory" srcDir = "tmp/local-cft-port/continuous-kummer-theory-main"`；
   该 `-main` 树与本 port 树 `diff_count=0`（19/19 文件逐字节相同）。其 `lake build` 已用当前工程
   Lean/Mathlib 产出 18/19 模块 olean（除 root 外全部，见 §3 "project lake lib" 列）。即：**这批源码在
   Lean 4.32.2 / Mathlib 905b958 下可原样编译，无需修 API**。
2. **瞬时错误（非源码错误）**：
   ```
   error: ...Basic.lean:6:0: failed to read file '...\mathlib\.lake\build\lib\lean\Mathlib\Analysis\LocallyConvex\SeparatingDual.olean.private'
   ```
   随机落在不同 Mathlib 模块；被报文件确实存在（如 SeparatingDual 898,872 B、Descent 344,232 B、Nobeling/Span 596,152 B）。
   与机器负载强相关：观测到 18 个 lean 进程、~21 GB working set、可用物理内存 ~4.4 GB；数学库 olean 的
   mtime 未变（未发生 mathlib 重建）。同一命令重试即成功（Basic 133.4 s、Comparison 170.2 s）。
   并行 worker 的日志（`tmp/local-cft-port/README-port.md`、`_s2052_*.log`）记录到同类错误，确认全机现象。
3. **root 模块**：`ContinuousKummerTheory.lean` 一次尝试 EXIT=1（82.5 s），错误是
   `object file '...\.lake\build\lib\lean\ContinuousKummerTheory\Kummer\Basic.olean' ... does not exist`
   ——并发 `lake build` 正在重建该共享目录，读取方撞上"oleans 被删除/替换"。属共享产物竞争，非本树源码问题。
   （建议本树编译时让 port 根优先于工程 build 目录，或等共享 lake build 结束后重跑。）

## 5. 复现脚本与日志（均在 port 树内）

- `_s2050_build4.ps1`：按拓扑序逐文件编译，带 8 次瞬时错误重试、跳过新鲜 olean、记录 attempts/secs。
  （`_s2050_build.ps1`/`_s2050_build2.ps1`/`_s2050_build3.ps1` 为早期版本；build3 的瞬时检测误读 stderr，已废弃。）
- `_s2050_root.ps1`：root 模块单独编译。
- `_s2050_logs\`：每模块 `<module>.log`（stderr）与 `<module>.out.log`（stdout+EXIT/SECONDS），以及 `summary*.tsv`。

## 6. 结论与下一步

- **第一里程碑（全部 EXIT=0 或精确错误清单）目前是"部分 + 精确错误清单"**：未发现任何 Lean 源码/API 错误；
  唯一阻塞是并发环境下 Mathlib olean 的瞬时读失败与共享 lake 产物竞争。证据：18/19 模块同字节源码已在
  当前工程成功编译出 olean。
- 可执行下一步（按代价排序）：
  1. 负载下降后直接重跑 `_s2050_build4.ps1`（带重试）；
  2. 或把工程 lakefile 的 `ContinuousKummerTheory` `srcDir` 指向本 port 树并 `lake build ContinuousKummerTheory`，
     一次得到 19/19（含 root）到 `.lake/build/lib/lean`；
  3. 再做 axiom 审计（`#print axioms` 三端点）与 Iut 消费者 import 探针。

## 7. 未运行

- 未运行 axiom/comparator 审计；未做 Iut 侧 import 消费者验证；未做全 Project 构建。
