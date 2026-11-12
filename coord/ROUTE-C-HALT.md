# C 路线停止记录（按用户指令，2026-11-12）

## 结论：C 路线当前不可行（两层原因）

### 1) 装配壳是循环的
- `Mzk1CRouteAssemblyActual.CRouteAssemblyInput.E7_radicalBound` 的类型就是 ABC 不等式本身：
  `∀ ε>0, ∃ C, ∀ a b c, IsABCTriple a b c → c ≤ C·(rad(abc))^(1+ε)`。
- 因此 `abcConjecture_of_cRouteAssembly` 等价于「ABC ⇒ ABC」；该文件头已自注 `E7_radicalBound` 为 ABC-strength 输入。
- 即：把目标直接放进了假设，不构成归约。

### 2) 非循环的真实目标是 δ 界，但它给不出标准 ABC
- 真实数学内容 = `δ_{N,1} ≤ N^(2+ε)`（等价 `h(E) ≤ (½+ε)log N + C`，半稳定 E）。
- 若证出，经 height/RT/Petersson 得 `logΔ ≤ (6+ε)log N`（Szpiro-6），Frey 代入给 `log c ≤ (3+ε)log rad`，
  即 ABC 的**指数 3 弱形式**，不是标准 ABC(1+ε)。
- 文献现状（已核）：P2026 只到 `h(E) ≪ N log log N`（半稳定外 `≪_S N`），距所需 `h ≪ log N` 有本质差距；
  P2018 只有 δ 的相对比较（Thm 1.5），无绝对 δ 上界。故 δ 界属研究前沿。

### 3) 结论
- C 路线作为「证明 ABC 的路径」在当前形式下不可行：装配循环 + δ 界未证且不等同标准 ABC。
- 保留为可复用的形式化设施：Frey 不变量/估值、L1–L7 算术、E7 归约接口、外部定理登记、证据隔离审计。
- 若要继续，真正需要的是新的**一致高度/导子界机制**（Pasten 的 Brandt/谱隙方向或 IUT 的 Θ-link 方向），不是接线。

## 停止时状态
- 8 个 teammate 已全部停止（inactive）。
- A/B/D/E 路线此前已停止；C 路线现停止。
- ABC gate 未通过；无无条件 ABC 结论。