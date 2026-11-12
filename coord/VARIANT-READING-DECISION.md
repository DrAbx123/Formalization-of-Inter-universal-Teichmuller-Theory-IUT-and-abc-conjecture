# VARIANT-READING-DECISION — concreteVariantData 的 S 选择与 lit/iv 判定 (A1028)

| field | value |
|---|---|
| Status | **DECISION: lana `concreteVariantData` 用 iv（单 label）；paper IUT III Cor 3.12 是 lit（全 label union），IUT IV Steps (iv)-(v) 是 iv；ABC 链（lana MainTheorem）用 iv。A1027 最小模型下 iv q-不稳定、lit 稳定 ⇒ 形式化/paper 偏差记录，目标选择需 owner 决策** |
| 源 | ThetaRegion:315-316 (`thetaPilot := thetaPilotOn _ (ivLabels _)`), :320-336 (`rhsDataOn`/`rhsData := rhsDataOn ivLabels`), :338-341 (`rhsDataLit := rhsDataOn litLabels`), :354-370 (`concreteVariantData`/`concreteVariantDataLit`), :372-384 (`Cor312VariantHolds`/`Cor312LiteralHolds`); Statement:66-91 (`Corollary312VariantData`, `Corollary312Variant := lhs ≤ rhs`); LeftHandSide:90-93 (`lhs = -absLogQ`); Literal.lean (`cor312Literal_of_variant`) |

## 1. lana 的 S 选择（精确行号）

- `Iut/Concrete/ThetaRegion.lean:315-316`：`thetaPilot := thetaPilotOn n (ivLabels n) (ivLabels_nonempty n)`；
- `:333-336`：`rhsData := rhsDataOn (ivLabels _) (ivLabels_nonempty _)`；
- `:338-341`：`rhsDataLit := rhsDataOn (litLabels _) ...`；
- `:354-362`：`concreteVariantData` 的 `rhsData := D.rhsData`（**iv**）；
- `:364-370`：`concreteVariantDataLit` 的 `rhsData := D.rhsDataLit`（**lit**）；
- `:372-376`：`Cor312VariantHolds := ∀ D, Corollary312Variant (concreteVariantData D)`（**iv**）；
- `:378-384`：`Cor312LiteralHolds := ∀ D, Corollary312Variant (concreteVariantDataLit D)`（lit）；
- `Iut/Cor312/Statement.lean:89-91`：`Corollary312Variant X := X.qPilot.lhs ≤ X.rhsData.rhs`；
  `LeftHandSide.lean:90-93`：`lhs := -Q.absLogQ`。
⇒ **lana 的 `concreteVariantData` 与 `Cor312VariantHolds` 都是 iv（S={j}）**；lit 版本单独定义。

## 2. paper 语义（IUT III/IV）

- IUT III, Corollary 3.12：theta-pilot hull 取 (Ind1) 的 label 置换（S_{j+1} 全集）⇒ **lit**
  （ThetaRegion:58-66 与 :73-74 的文档明确：literal union 由 min_l ord 控制）；
- IUT IV, proof of Theorem 1.10, Steps (iv)-(v)：只取 label j（S={j}）⇒ **iv**；
- lana 的 ABC 桥 `Iut.MainTheorem.lean:13 classicalABC_of_variant : Cor312VariantHolds → ClassicalABC`
  用 **iv**；`Literal.lean cor312Literal_of_variant : Cor312VariantHolds → Cor312LiteralHolds`（iv ⇒ lit）。
- Statement.lean:55-59 明确："The intended statement may differ from the formulation printed in the
  IUT papers... the concrete inputs are the project's concretization"。

⇒ 对 **ABC 链（我们的目标）**，iv 是 lana 的操作目标；lit 是较弱的独立版本。

## 3. A1027 最小模型的判定

（模型：e=1, shell=O, n=1, qroot ord = m/(2ℓ), A = m logp/(2ℓ), sF = (1/nC)Σj²）

| reading | ind2 | gap | variant 条件 | 稳定性 |
|---|---|---|---|---|
| **iv** | 0 | 0 | `V ≥ (sF-1)A` | **不稳定**（V q-无关、RHS 线性无界） |
| **lit** | +j²A | sF·A | `V ≥ -A` | **稳定**（V≥0, A≥0 ⇒ trivially true） |

**lit 化简**：`gap = sF·A ≡ V + gap = V + sF A ≥ (sF-1)A ⇔ V ≥ -A`；
若 `V ≥ 0`（hull(vcI) 的 packet 体积非负；finite tame 公式 `Σ(1-1/e)logp ≥ 0`，
arch/infinite 为 log-shell 半径 `logShellRadius ≥ 0` 型），则 `V ≥ 0 ≥ -A` ⇒ lit variant 真。
**GAP-VNONNEG**：`V ≥ 0` 需要 `logShellRadius ≥ 0` 与 packet 体积非负的 green 引理（未验证）。

## 4. 判定与偏差登记

1. **lana 用 iv，paper IUT III 用 lit，ABC 桥（MainTheorem）用 iv**；
2. A1027 模型：iv q-不稳定（大 qOrder 下 `V ≥ (sF-1)A` 被破坏），lit q-稳定；
3. 因此若 A1027 模型忠实，**lana 的 iv 目标对任意 I_n 大数据为假**（或我们的模型/归一化有误）；
   这与 IUT 定理矛盾，说明偏差存在（候选：θ-pilot 的 q 指数非 j²、A 与 qOrder 归一化差 2ℓ、
   V 含 q 项、或 iv 实际也取 Ind1 平均）；
4. **不擅自改目标**（目标锁定原则；改目标需用户指令）；记录偏差并上报 lead/owner：
   - `FINAL-STATUS` 增行："iv/lit 读法分歧：lana concreteVariantData=iv；A1027 模型 iv q-不稳定、lit 稳定；
     ABC 桥用 iv；待 owner 决策"；
   - `AUDIT-LEDGER` 记同一事实；
5. 若 owner 决定以 lit 为目标：ABC 链需新桥（lit ⇒ ABC）或回到 paper 的 iv 归一化修订。

## 5. Lean 陈述（草案）

```lean
/-- iv variant unfolding (Statement:89-91). -/
theorem variant_iv_iff (D : InitialThetaData) :
    Corollary312Variant (concreteVariantData D) <->
      (sFactor (nC D) - 1) * D.qPilot.absLogQ <=
        logVol D (hullOf D (vcI D)) + gap D := by
  rw [corollary312Variant_iff, variant_iff_le_rhs]
  have h := gap_eq_rhs_add D
  linarith

/-- lit variant: gap_lit = sF*A implies V >= -A (trivial if V >= 0, A >= 0). -/
theorem variant_lit_of_gap (D : InitialThetaData)
    (hgap : gapLit D = sFactor (nC D) * D.qPilot.absLogQ)
    (hV : 0 <= logVol D (hullOf D (vcI D)))
    (hA : 0 <= D.qPilot.absLogQ) :
    Corollary312Variant (concreteVariantDataLit D) := by
  rw [corollary312Variant_iff, variant_iff_le_rhs]
  have h := gap_eq_rhs_add_lit D   -- lit 版 gap_eq_rhs_add（需端口）
  linarith
```

## 6. 结论

- concreteVariantData = **iv**（源级确认）；paper IUT III = lit，ABC 桥用 iv；
- 最小模型：lit 稳定、iv 不稳定；故 iv 目标若忠实则存在偏差，**不擅自改目标**；
- 产出待 owner 决策：改 lit（需新 ABC 桥）、或修订 iv 归一化；
- GAP-VNONNEG（V≥0）与 lit gap 恒等式（gapLit=sF·A）需端口/证明；
- 本文件不修改生产文件；建议由 lead 决定后在 FINAL-STATUS/AUDIT-LEDGER 登记。