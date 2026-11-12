# S1487-SOURCE-ROOT — concrete instance identity (A1073)

| field | value |
|---|---|
| Status | PARTIAL（canonical logQ 的实例恒等式真证；paper logQ 兼容性是数据条件） |
| Lean | `tmp/sheaf/xif/paper/Mzk1S1487SourceRootIdentityActual.lean`（未编译；无 sorry/axiom） |

## 1. qParameter 是数据字段（源级）

- `S1487SourceData (Bad) [Fintype Bad] (q : Bad → Real) (hq0) (hq1) (hqne) : SourceDefinition31Data l`
  （S1487:400-424），`reduction.qParameter := q` —— **任意 Real 函数作为数据**；
- `S1487FaithfulSourceData := S1487SourceData PUnit (fun _ => ‖S1487Cand.q‖) ...`（S1487:520-524），
  即 `qParameter _ = ‖S1487Cand.q‖`，`badPlaces = PUnit`；
- 因此 `OrigXiFPaperBadQAbsLog S1487FaithfulSourceData = |Real.log ‖S1487Cand.q‖|`（单点求和）。

## 2. 结论：等式是数据条件，不是普遍定理

`paperQAbsLog l logQ = qNormFactor l * logQ = logQ/(2l)`；要等于 `badQAbsLog`，
**唯一**办法是取 `logQ := 2l * badQAbsLog`（数据选择），而不是从 paper 的
`logQ = Σ weight·qOrder·logp` 推出。故：
- `logQ := 2l*badQAbsLog` ⇒ 恒等式 **rfl/ring 可证**（本文件 `S1487_sourceRootIdentity`）；
- paper 的 `logQ_paper = Σ weight·qOrder·logp` 与 `2l*badQAbsLog` 相等 ⇒ 需 S1487 的
  `qParameter = ‖S1487Cand.q‖` 与 `qOrder/weight/residueChar` 的离散识别（GAP-PAPER-LOGQ）。

## 3. Lean（真证部分）

```lean
theorem paperQAbsLog_two_l_mul (l) (x) : paperQAbsLog l (2*(l.value:Real)*x) = x
noncomputable def S1487CanonicalLogQ (l) := 2*(l.value:Real) * OrigXiFPaperBadQAbsLog (S1487FaithfulSourceData (l:=l))
noncomputable def S1487RootInput (l) := S1487OriginalInput (S1487FaithfulSourceData (l:=l))
theorem S1487_sourceRootIdentity (l) :
  SourceRootIdentity (I := S1487RootInput l) (S1487CanonicalLogQ l)
def PaperLogQCompatibility (l) (logQ) := OrigXiFPaperBadQAbsLog (S1487FaithfulSourceData) = paperQAbsLog l logQ
theorem S1487_paperLogQCompatibility_canonical (l) : PaperLogQCompatibility l (S1487CanonicalLogQ l)
```

## 4. 判定

1. `reduction.qParameter` 是数据字段 ⇒ `badQAbsLog = paperQAbsLog l logQ` **不是普遍定理**；
2. 在 S1487 具体实例上，取 canonical `logQ := 2l*badQAbsLog` 时等式**真证成立**
   （`S1487_sourceRootIdentity`）；
3. 但 paper 的 `logQ`（来自 qOrder/weight/residue）与 canonical 值相等需要额外离散识别
   （GAP-PAPER-LOGQ）——这是 S2708 所述 finite-place/discrete-q 缺口的 S1487 具体化；
4. 因此 Route A 标量闭合**不能**只靠 S1487 数据完成；需把 paper q-divisor 的 logQ 与
   `2l*badQAbsLog` 的恒等式作为数据条件（或构造 placeOf/qFamily 证明之）。