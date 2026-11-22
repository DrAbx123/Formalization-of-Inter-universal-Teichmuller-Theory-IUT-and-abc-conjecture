# Unfinished 100% AI LeanFormal IUT audit project

## 从这里接手（2026-11-22）

> **时间或算力有限时，下次只追一个点。** 在 IUT III 推论 3.12 的固定算例中，从原文的求值构造出 $z=E_\tau(1)$，证明它属于第二行在素数 3 处的原允许区域 $U_{2,3}$。

**目前做到哪里。** 固定 $p=3,\ \ell=5,\ d=3$，用 `G` 表示好位、`B` 表示坏位。具体模型中，目标元组 `(G,B,B)` 的默认标记在槽 2，参考点的投影绝对值为 $3^{-6/5}$。交换槽 2 和槽 0 时，源元组 `(B,B,G)` 的标记好槽 2 随参考元 `1` 搬到目标好槽 0，各指定投影都是 `1`。这段模型计算已经完成。现在开放的是这次换位和落点在**同一原文输入**中的来源。[已有换位定理](Iut/Concrete/Ind1Invariance.lean#L592) · [交接 §19.3](coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#193-原文来源桥的精确形状)

1. **起点。** 打开 III 注记 3.10.2 的交换图，从下排第一条求值箭头 `env → gau`（引自 II 推论 4.10(ii)）开始。沿同一组跨列识别（IPL）跟踪 `(B,B,G)` 的点 `1`，每到一个对象就记下标记落在哪个槽。[原文交换图及箭头说明](coord/IUT-TEXT/III.txt#L9069)
2. **本次交付。** 写出目标列中原文允许的输出 $D_\tau$，说明它来自这个固定输入，给出 $z$ 在其中的位置和槽 0 的投影，证明 $z\in U_{2,3}$。若已得到该点在指定张量块上的乘法稳定满秩整格 $L$，只需检查乘以 $z$ 在 $L/3L$ 上的行列式非零，即可确认同一见证的各指定投影都是单位。[原文对允许像的定义](coord/IUT-TEXT/III.txt#L10376) · [模 3 检验及适用条件](coord/GRH-METHODS-FOR-IUT-20261122.md#iii312-固定输入上的判据)
3. **停止条件。** 拿到上述成员证明，就交接这个元组的结果。若某条箭头只给出未标记的标量或形式换位，就记下最后保有标记的对象、所缺映射的起点和终点，以及缺哪条原文依据，到此停手。

**通过后再扩展。** 先用同一求值与换位的相容性处理另一换位 `(2,1)` 和其余受影响元组，再按原文的秩与权重核对读数，得到固定输入的比较。一般输入的比较和原允许像的有限性仍待证明，后续才接 IUT IV 的高度估计与整数 ABC。[交接 §19.5](coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#195-暂停点验收和下一动作) · [项目目标](GOAL.md)

[心得](./心得.md)

This repository is a source-oriented, auditable Lean 4 project for the
bottom-up study of Mochizuki's IUT I--IV papers and the ABC bridge.  The
production entry point is `LeanFormal/IUT/Project.lean`; the root library
`LeanFormal.lean` imports that entry point only.

The ordinary arithmetic, theta-kernel, labelled-coordinate, and weighted-volume
foundations use Mathlib directly.  IUT-specific constructions are separated
from interfaces and marked obligations.  The Theorem 3.11 -> Corollary 3.12
Step XI contract remains open.  The repository has no accepted proof of IUT or ABC.

The source corpus and citation/dependency map are under
`papers/motizuki_corpus/`.  The per-module status and exact verification
history are maintained in `AUDIT_LEDGER.md`.

The previous independent real-analysis exercise is retained, but quarantined
at `LeanFormal/Archive/AnalysisExercise/Basic.lean` and is not part of the IUT
production entry point.

## Versions

- Lean: `v4.32.2`
- Mathlib: `v4.32.2`

## Verify

Run Lean verification through the watchdog. Add the affected `.lean` path to
[extra-targets.txt](dag/watchdog/extra-targets.txt) and read its `DONE` or `FAIL`
entry in `dag/watchdog/watchdog.log`. [Watchdog instructions](coord/LEAN-INDEX.md)

# If it've benefited your project, I'll more than excited.
# It's paused cause the ability of the AI is far more than enough to achieve the goal
