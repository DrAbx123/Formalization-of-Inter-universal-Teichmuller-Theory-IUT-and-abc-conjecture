# C9 adversarial review：ThreeAssumptions 的 circularity / axiom boundary

任务：task-464（Circularity audit of ThreeAssumptions）。owner：iplsheapt。日期：2026-10-25。只读审计；不改任何 Lean 源（含 volumedet 文件）；只写本文件。No mixed/E3。

被审对象：`tmp/sheaf/n8/closure/C9Cor312ThreeAssumptions.lean`；对照 `C9ThreeAssumptionsCountermodel.lean`；`tmp/review-three-build-20261025/C9Cor312ThreeAssumptionsAudit.lean`。

## 0. Verdict

**C9Cor312ThreeAssumptions 没有从 A1-A3 证明 C1；它通过 `Theorem311Full.qPilotOutput_mem` 直接假设了 C1 的一个 witness，再通过 `sourceThreeAssumptions` axiom 把整个 package 作为全局公理。** 因此 `cor312_unconditional` 不是“unconditional C1 from source”；它只是“if C1 witness is assumed then C1”。如果该文件被当作 source proof 或 target closure，axiom boundary **不诚实**。

`cor312` 本身的证明是有效的、几乎 tautological：qPilotOutput_mem ⇒ qLog∈R；hull_upper ⇒ qLog≤h。问题在于前提，不在推导。

## 1. Exact Lean content

`Theorem311Full` 有字段：

```
Output : Type
possibleOutputs : Set Output
logVol : Output → ℝ
qPilotOutput : Output
qPilotOutput_mem : qPilotOutput ∈ possibleOutputs     <-- C1 witness
```

`Prop39` 给 `qLog` 与 `qLog = logVol qPilotOutput`；`Remark395` 给 `R = logVol '' possibleOutputs` 和 `hull_upper : ∀x∈R, x≤h`。`ThreeAssumptions` 只是三者 bundle。

证明：

```lean
have hq : qLog ∈ R := by
  rw [R_eq, qLog_eq]
  exact ⟨qPilotOutput, qPilotOutput_mem, rfl⟩
exact hull_upper qLog hq
```

`sourceThreeAssumptions : ThreeAssumptions` 是全局 `axiom`；`cor312_unconditional` 使用它。

## 2. Is qPilotOutput_mem C1?

C1: `∃ D0∈O, logVol(D0)=Q`，其中 `Q=-|log q|` 是 q-pilot log-volume。

`qPilotOutput_mem` 给出一个**指定的** `qPilotOutput`，且 `qLog=logVol qPilotOutput`。因此它给出 C1 的 witness：

```
C1 witness: D0 := qPilotOutput;  logVol(D0)=qLog=Q.
```

所以 `qPilotOutput_mem` **蕴含 C1**（实际上比 C1 更强：它固定了一个 q-pilot output，而不是仅存在某个 output）。`cor312` 从它推出 inequality，不奇怪；这是把 C1 作为字段再用。

## 3. Source justification?

文件 docstring 声称 `Theorem311Full` 是“Theorem 3.11, full content needed here: ... the fixed/coric q-pilot input rigidification is one of them (IPL + final evaluation map).”

这个 claim **不是** Theorem3.11 的 source 内容。IUT III Theorem3.11 给 multiradial construction algorithm、possible outputs、IPL/SHE/APT/Ind1-3；它**没有**断言 q-pilot input rigidification itself 是 possibleOutputs 的元素。那正是 xi-e/xi-f compatibility（C1），也是所有 C1 audit 中反复出现的 missing membership。因此把 `qPilotOutput_mem` 放在 `Theorem311Full` 里面，等于把待证 C1 改名为 Theorem3.11 的字段。

`Prop39.qLog_eq` 和 `Remark395.R_eq/hull_upper` 也是抽象 schema，不是已构造的 source objects；但决定性问题在于 `qPilotOutput_mem`。

## 4. Axiom boundary

`sourceThreeAssumptions` 是 **自定义全局 axiom**，不是 source theorem，也不是允许的 `propext/Classical.choice/Quot.sound`。它断言存在一个 `ThreeAssumptions` package；而该 package 的第一分量已经包含 C1 witness。

因此 `#print axioms cor312_unconditional` 会显示 `sourceThreeAssumptions`（以及可能的基础公理）；`cor312_unconditional` 的 kernel closure 依赖这个自定义 axiom。它不是 target-accepted proof。若把 `sourceThreeAssumptions` 当作“A1+A2+A3”的缩写，则缩写**隐藏了 C1 假设**，axiom boundary 不诚实。

诚实的形式应是：

```
theorem cor312_conditional
  (A : ThreeAssumptionsWithoutMem)
  (hmem : A.T311.qPilotOutput ∈ A.T311.possibleOutputs) :
  A.P39.qLog ≤ A.R395.h
```

其中 `hmem` 被明确命名为 C1/xi-f membership；不要用 `axiom` 关闭它，也不要把 `Theorem311Full` 命名成含 membership 的 source theorem。

## 5. Countermodel / A1-A3 independence

`C9ThreeAssumptionsCountermodel.lean` 去掉了 `qPilotOutput_mem`，保留其余 abstract A1/A2/A3 字段，并给出：

```
Output := Unit; possibleOutputs := ∅; logVol := 1; qPilotOutput := ();
qLog := 1; R := ∅; h := 0;
```

它满足所有剩余字段，但 C1 为 `1≤0` false。`qPilotOutput_mem` 在该 model 中不可能成立，因此它是 load-bearing。该文件还证明：加入 membership 后 C1 立刻可证。

这个 countermodel 是 **abstract formal independence**，不是 actual admissible C；它不反驳源定理，但足以说明：从去掉 `qPilotOutput_mem` 的 A1/A2/A3 schema 推不出 C1。主文件把 membership 放回 `Theorem311Full`，所以不是“证明”而是“假设”。

## 6. Comparison with abstract A1-A3 independence

| item | status |
|---|---|
| abstract A1 + A2 + A3 without qPilotOutput_mem | consistent with C1 false (countermodel) |
| qPilotOutput_mem | independent extra field; exactly C1 witness |
| ThreeAssumptions with qPilotOutput_mem | C1 assumed, not proved |
| cor312 proof | valid conditional/tautological derivation |
| sourceThreeAssumptions axiom | extra global axiom, hides C1 |
| `cor312_unconditional` as unconditional C1 | **REJECT** |

## 7. What is honest

1. Rename the structure: `Theorem311PlusC1Witness` or keep `Theorem311Full` but mark `qPilotOutput_mem` as the open C1 hypothesis. Remove the sentence “Theorem3.11, full content ...” — it overclaims source content.

2. Do not declare `axiom sourceThreeAssumptions : ThreeAssumptions`; use a theorem parameter/hypothesis, and report its axiom dependencies.

3. Report `cor312` as: `C1 witness ⇒ Cor3.12 inequality`, not as `A1+A2+A3 ⇒ C1`.

4. The real remaining obligation is exactly `qPilotOutput_mem` / xi-f membership; the ThreeAssumptions package has not reduced it.

## 8. Conclusion

C9Cor312ThreeAssumptions does not prove C1. Its `Theorem311Full` structure contains `qPilotOutput_mem : qPilotOutput ∈ possibleOutputs`, which is precisely a C1 witness; `cor312` is then a valid tautological derivation, and `sourceThreeAssumptions` is a custom axiom that assumes the whole package. The abstract A1-A3 countermodel without membership shows the membership is independent/load-bearing. Therefore the axiom boundary is dishonest if this is presented as unconditional C1 from A1-A3; it is honest only as the conditional statement “if a q-pilot output is possible, then C1”. No Lean edits were made; no mixed/E3; P6/C1 remain open.

