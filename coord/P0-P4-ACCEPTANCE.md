# P0–P4 验收清单（Lead 维护，2026-11-13 晚）

## 通用验收（所有新文件）
1. `lake env lean` / watchdog DONE + olean 存在（build 证据）。
2. `#print axioms 主定理` ⊆ {propext, Classical.choice, Quot.sound}；无 `sorryAx`。
3. 源代码扫描：无 `sorry`/`admit`/`axiom`/`PUnit`/`: True` 占位（Lead 已对 63 个最近文件扫描：0 命中）。
4. 禁止：`IsEmpty.elim` 或空类型消去推出比较；`Nonempty`/`Prop := True` 空包装当构造；toy carrier/value-layer surrogate。
5. 缺口必须精确命名（引理名/字段/所需数据），不得以 named input 冒充已证。

## P0（native 源接回）
- [ ] native 输入（T,b,p,places,tuple）→ core（roots 在代数闭包/qVFamily/qVFamTensor*）编译通过；
- [ ] core→readout→tensor consumer 至少一条端到端链编译通过；
- [ ] 旧 C3 消费者迁移表（活动组 43/100/13/5）逐组给 native 替代或精确不可替代；
- [ ] 无旧 C3 构造、无 IsEmpty 消去。

## P1（B5 生成元/count）
- [ ] `localizedLine I v = span O_v {generator}` 与/或 `localValuation v generator = -countExponent v I` 真证；
- [ ] 若仍缺：单一精确缺失引理名（DVR/localization count）；
- [ ] 含 f_v 的 B5 输出定理（`PlaceB5WithFv` green 已有）。

## P2（一个真实标签块 + 质量差）
- [ ] R1.2：选实际 (p,tuple,label)，写出 `g^q_a = Σ c_ia g^θ_i` 完整展开，展示源 q/源 θ/落点/权重四来源；
- [ ] 系数整性（单生成元/纯张量/有限和已 green；完整版待）；
- [ ] R1.3：`R_exact = Σd_b(log‖λ‖−log‖qhat‖) = −Σd_b log‖c_b‖ ≥ 0`；与 `c0RemainderV2` 的 correction 显式对齐（不假设相等）。

## P3（迹下降）
- [ ] (R3.1) 分块+真实域分解映射；(R3.6) 迹对偶系数；(R3.7) 精确指数——至少可编译并给出净量非负第一步；
- [ ] 不使用旧 C3 inhabitant（P3 core 参数化）。

## P4（闭合，暂不启动）
- [ ] 从原合格输入内部构造全部对象并连回原 q/Theta 目标；
- [ ] `target_accepted`、独立审查、comparator 验收（目前 NOT_RUN）。

## Lead QA 命令（可复用）
```powershell
# 最近文件 sorry/axiom/PUnit/True 扫描
$recent = Get-ChildItem 'D:/lean/tmp/sheaf/xif/paper' -Filter '*.lean' | Where-Object { $_.LastWriteTime -gt (Get-Date).AddMinutes(-90) }
$recent | ForEach-Object { Select-String -Path $_.FullName -Pattern '\bsorry\b|\badmit\b|^axiom |\bPUnit\b|:\s*True\b' }
```
