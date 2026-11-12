# A498: stage4 theta hull 资产 vs paper theta-pilot（同测度/同归一化核对）

范围: AbsTopIII09ThetaHullScalingActual、S3137ThetaHullVolumeScalingActual、GlobalThetaPilotLogVolumeActual、GlobalPositiveThetaHullLogVolumeActual（均 green olean；只读）。paper: IUT III Def 3.8(i)/Cor 3.12 L10324-10353；III Prop 3.9 L6838+；IV L1358-1363/1746-1753。

| 文件 | 关键 decls | 构造内容/测度 | paper 对象 | 忠实性判定 |
|---|---|---|---|---|
| AbsTopIII09ThetaHullScalingActual | absTopIII_thetaHull_log_measure_prime_smul(L52)、absTopIII_thetaPilotHullLogVolumeReal_eq_actualRegion(L62) | 只是 S3137 两定理的别名/包装（imports + 复用，无新证明） | λ-O log-volume 的 p-scaling（IUT III Prop 3.9(i)） | 包装层忠实（相对 S3137），本身无独立对象 |
| S3137ThetaHullVolumeScalingActual | thetaPilotHull(L97)=actualHolomorphicHull(unitRegion)=actualC3LogShellTensorRegion；thetaPilotHullLogVolumeReal(L128)=log(actualC3LogShellTensorHaar(hull)); measure_lt_top(L51); prime_smul(L59) | `actualC3LogShellTensorHaar := Measure.addHaar` 于 Q_p-tensor block；hull=单个 λ-O tensor log-shell 区域；p-scaling law | IUT III Prop 3.9(i) 的局部 λ-O log-volume 归一化；但非 Θ-pilot object 的 hull/union/procession average | **部分忠实**: 测度为 additive Haar（仅 up-to-constant；p-scaling law 对任何 additive Haar 自动成立），绝对 log-volume 非 paper normalized；对象是单 tensor 区域不是 Θ-pilot hull。qThetaPilotLogVolumeComparison(L145) 仍是 pending Obligation |
| GlobalThetaPilotLogVolumeActual | baseQReal(L60)=||baseQ.q||; thetaValueFromQ(L75)=baseQReal^{gaussExponent j}; localThetaLogVolume(L99)=card(SignedLabel)^{-1}Σ_j(-log theta); globalThetaPilotLogVolume(L105)=Σ_b local; localThetaLogVolume_eq(L110) | 值层平均: 对 SignedLabel（card l，含 0）的 q^{j²} 平均值，再对 V_bad 求和；无 hull/union/Haar | paper Θ-pilot 的 theta values 平均值候选（-|log Θ| 的近似） | **不完全忠实**: (a) baseQ 是 full q（非 q_v=q^{1/2ℓ}）⇒ log 尺度差 2ℓ；(b) 平均除以 card=l（含 0）而非 F_l^⋇ card=l−1 ⇒ 系数差 (l−1)/l；(c) 无 hull/possibleImage union；docstring 自述 candidate only。公式 global=(gaussExponentSum/card)·globalQPilotLogMagnitude 仅值层恒等式 |
| GlobalPositiveThetaHullLogVolumeActual | thetaPositiveLogVolumeAt(L42)=-log(I.thetaValueAt n 0 j); thetaHullPositiveLogVolumeAt(L64)=Σ_j(...); globalThetaHullPositiveLogVolume(L79)=Σ_v(...); GlobalPositiveThetaHullLogVolumeData(L90) | 对 abstract I.thetaValueAt/thetaPacket.logVolume/sourceHolomorphicHull/SourceImageRealization 的 value-realization 数据；Σ_j 与 Σ_v（非平均、无 Haar）；thetaHullPositiveLogVolumeAt_eq(L70) 只是 packet.logVolume 定义恒等式 | paper Θ-pilot hull log-volume | **不忠实/不可用**: 无真实 hull 测度（sum of -log theta values），无 procession 平均/权重；使用 value-model SourceImageRealization（A481/F2 规则不可作 IUT 对象证据）；不是 Haar log-volume |

## 结论
1. 四个资产中只有 S3137 有真实对象（C3 tensor log-shell 区域的 additive Haar log-volume）与 IUT III Prop 3.9(i) 的局部归一化行为；AbsTopIII09 是它的包装；二者都不是 paper Θ-pilot object 的 hull/union/procession-normalized log-volume，且 Measure.addHaar 只有 up-to-constant 归一化。
2. GlobalThetaPilotLogVolumeActual 是值层 theta-values 平均候选，但 q/2ℓ 与 label-average 两处归一化与 paper 不符（2ℓ·(l−1)/l 级），且缺 hull/union ⇒ 不能当 -|log Θ|。
3. GlobalPositiveThetaHullLogVolumeActual 使用 value-model 的抽象 thetaValueAt/sourceHolomorphicHull，且以和代替平均、无 Haar ⇒ 不可作 paper Θ-pilot 证据（F2 规则）。
4. 依 A499 对象优先：需按 paper 构造 Θ-pilot object（product over j∈F_l^⋇、2ℓ roots、Ind1/2/3 union、holomorphic hull、procession normalization），再谈比较；不要接线。

只读；未改文件/队列/watchdog。