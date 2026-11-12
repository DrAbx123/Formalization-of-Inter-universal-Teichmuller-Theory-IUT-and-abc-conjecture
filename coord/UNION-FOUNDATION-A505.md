# A505 联合地基（Union Foundation）策略

用户指示：不手写太基础的东西；把仓库里已有的外部基础（Fermat/TauCeti/Belyi/其他 GitHub 项目）+ 最新 Mathlib 用脚本转码/移植，全部编译好，然后只在其闭包之上构造我们真正缺的对象。

## 已可用的地基（全部在树内、import 可直接用）
1. **Mathlib v4.32.2**（当前 lake require）
2. **local-cft-port**：`tmp/local-cft-port`（PadicField/Reciprocity/ClassFieldAxiom/Galois/Herbrand/Brauer/ContinuousKummerTheory，lake lib 已注册）
3. **已移植 foundation（脚本转码，import 已改写）**：`tmp/external/ported/`
   - TauCeti 系：tauceti2(264)、tauceti_rr(263)、tauceti_belyi_rr(183)、tauceti_belyi_ff(174)、tauceti_belyi_core(6)
   - Fermat 系（fermats-last-theorem）：flt(19)、flt_core(234)、flt_th(239)、flt_test(224)
   - Belyi 系：belyi_pair(276)、belyi_pair_scheme(276)、belyi_poly(5)
   - 形态：`import tmp.external.ported.<pkg>.<原模块>`；文件头有来源/license 说明
4. **Takkun-IUT_LEAN**：已移植 `tmp/sheaf/takkun/IutLean/`（68 模块；对象层+辅助数学），import 改写 `tmp.sheaf.takkun.IutLean.*`
5. **自有**：`LeanFormal/IUT`（1,187）+ 根 `Iut/`（256 Foundations）+ `tmp/sheaf/xif/paper`
6. 待移植候选：`tmp/external/promachina-iut-lean-latest`(200)、`tmp/external/iut4-sec1`（IUT IV §1）、`tmp/external/PriestAmbrose-IUT-Corollary3_12-Lean`

## 工具
- `tools/extras_add_closure.mjs <files...>`：从目标 Lean 文件计算 import 闭包（全仓模块映射），把闭包全部加入编译队列（lock/去重/原子写）。
- `tools/port_lana_explicit.mjs`/`port_takkun.mjs`：外部 repo → 树内 + import 改写 + 闭包清单。

## 工作方式
1. 需要某基础引理时：先 grep 联合地基（Mathlib/local-cft/ported/Takkun），找到就直接 import；若其模块无 olean，用 `extras_add_closure` 把闭包入队交给 watchdog。
2. 只有联合地基完全不覆盖时，才手写；且必须 `_constructed`/真实定义。
3. 不为'基础'再开新项目；优先复用。
4. 已编译的 ported 基础只在 build 有 1 个 olean/包（未全编）；用到哪个模块就入队其闭包。