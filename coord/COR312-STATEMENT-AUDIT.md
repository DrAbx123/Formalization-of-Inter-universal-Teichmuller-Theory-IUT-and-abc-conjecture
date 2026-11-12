# COR 3.12 STATEMENT AUDIT (A497/A498)

作者: stepxi. 对照 IUT III Corollary 3.12 原文，审计 StepXIContract / Cor312Conclusion 与 qTheta 读法。只读/文档；不改实现。

## 1. Paper Cor 3.12 (IUT III text 10324-10353, 869-899)

- q-pilot object: bad places v in V_bad 上 q_v 的 zero locus 决定的 arithmetic divisor，位于 global realified Frobenioid 的 domain。
- Theta-pilot object: bad places 上 theta values 集合 {q^{j^2}_v}_{j=1,...,l*} 的 zero locus 决定的 arithmetic divisor。
- theta values 是 2*l*-th roots 体系: 论文 10215 明确 theta values 只 up to multiplication by 2*l-th roots of unity; 在 IUT 中 q 是 Tate parameter，theta values 是 q 的 2*l-th root 的 j^2 次幂。
- -|log(Theta)|: Theta-pilot object 在 multiradial representation 中的 possible images 的 union，受 Ind1/Ind2/Ind3 作用，取 holomorphic hull，再取 procession-normalized mono-analytic log-volume（见 Remark 3.1.1, Proposition 3.9, Theorem 3.11）。
- -|log(Theta)| 取值在 R union {+inf}; Cor 3.12 先断言它属于 R（有限），再断言 -|log(Theta)| >= -|log(q)|。
- 等价形式: 对任何实数 C_Theta 满足 -|log(Theta)| <= C_Theta * |log(q)|，有 C_Theta >= -1。
- j^2 average: procession normalization 对 j in F_l^x 取平均（Remark 3.1.1）；LANA 侧把该 average 的算术部分写成 sFactor(nC) = (sum_{j=1..n} j^2)/n = (n+1)(2n+1)/6，nC=(ell-1)/2。paper Cor 3.12 的 log-volume 必须包含该 procession normalization，而不是一个裸实数。

## 2. 我们的 Lean 定义（逐字）

StepXIContract / Cor312Conclusion (LeanFormal/IUT/IUTIII/Corollary312/StepXI/Contract.lean):

    structure StepXIContract where
      qSigned : Real
      thetaSigned : Real
      targetSigned : Real
      q_negative : qSigned < 0
      ipl : Prop
      she : Prop
      apt : Prop
      ipl_evidence : ipl
      she_evidence : she
      apt_evidence : apt
      q_le_target : qSigned <= targetSigned
      target_le_theta : targetSigned <= thetaSigned

    def Cor312Conclusion (contract : StepXIContract) : Prop :=
      contract.qSigned <= contract.thetaSigned

qTheta 读法 (Mzk1QPilotR4Stage5AlignActual / Mzk1QPilotSHEDoubleImageActual):

    noncomputable def qPilotLogImage (b : Bad (nativePlaceSelection T)) : Real :=
      localSignedLog (qVFamily T b)
    -- localSignedLog q = Real.log ||q||

    def thetaPilotLogImage (b) : Real :=
      qPilotLogImage T b / (2 * (l.value : Real))
    def qThetaHullReadout (b) : Real := qPilotLogImage T b
    def qThetaDetReadout (b) : Real := thetaPilotLogImage T b

    def qThetaStepXIContract (b) (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
        StepXIContract where
      qSigned := qPilotLogImage T b
      thetaSigned := thetaPilotLogImage T b
      targetSigned := thetaPilotLogImage T b
      q_negative := qPilotLogImage_neg T b
      ...
      q_le_target := le_of_lt (qPilotLogImage_lt_thetaPilotLogImage T b)
      target_le_theta := le_rfl

## 3. 与 paper 的逐项差异

### 过弱（statement 丢失 paper 内容）

1. 没有 q-pilot object / Theta-pilot object，也没有 arithmetic divisor / zero locus；qSigned, thetaSigned 是任意 Real。
2. 没有 bad places V_bad，没有 q_v，没有 theta values {q^{j^2}}，没有 j=1,...,l* 的指标。
3. 没有 2*l-th root 体系；我们的 thetaPilotLogImage 定义为 q / (2*l)，不是 q 的 2*l-th root 的 j^2 次幂。
4. 没有 Ind1/Ind2/Ind3 possible images 的 union；ipl/she/apt 是任意 Prop。
5. 没有 holomorphic hull；thetaSigned 不是 hull 的 log-volume。
6. 没有 procession normalization / j^2 average；没有 sFactor(nC) 或平均因子。
7. 没有 finiteness 结论 -|log(Theta)| in R；Cor312Conclusion 没有 +inf 排除。
8. 没有 C_Theta 形式；不能推出 C_Theta >= -1。
9. 没有 q-pilot log-volume 的独立构造；q_negative 只是裸负数条件。
10. 没有 global realified Frobenioid / mono-analytic representation 的对象。

### 过强/额外但空转

1. targetSigned 是 paper 没有的中间量；任何 q<=theta 都可取 target=theta，使 target_le_theta = rfl。
2. q_le_target 与 target_le_theta 只是把 q<=theta 拆成两个字段；Cor312Conclusion 由 le_trans 得到，没有独立数学内容。
3. qThetaStepXIContract 取 targetSigned := thetaSigned，故 target_le_theta := le_rfl；比较字段完全空转。
4. qThetaReadout_ordered 只是 q < q/(2*l)（q<0, 2*l>1）的负数除法算术恒等式。
5. qThetaFourTriangleSynthesis.step3115_comparison 就是上述算术恒等式；不能作为 paper Cor 3.12 的比较。

## 4. qTheta 空转链（精确）

qPilotLogImage = Real.log ||q_V||（单点局部 signed log，不是 global q-pilot log-volume）。
thetaPilotLogImage = qPilotLogImage / (2*l.value)（定义，不是 Theta-pilot）。
qThetaHullReadout = qPilotLogImage；qThetaDetReadout = qPilotLogImage/(2l)。
qThetaStepXIContract: qSigned=qPilotLogImage, thetaSigned=qPilotLogImage/(2l), targetSigned=thetaSigned。
q_negative: qPilotLogImage<0; q_le_target: q < q/(2l) (negative division); target_le_theta: rfl。
因此 step3115_comparison_proved 与 Cor312Conclusion 只证明 2l>1 时负数 q 小于 q/(2l)，不是 Cor 3.12。

## 5. 重建后的忠实 statement 草案（未实现，仅规格）

    structure ThetaPilotData (D) where
      bad : Finset (FinitePlace D.F) -- V_bad
      qroot : (v : bad) -> Completion v -- chosen 2*l-th root, qroot^(2*l)=q_v
      thetaValue : (v : bad) -> Fin lStar -> Completion v
      thetaValue_eq : thetaValue v j = qroot v ^ (j+1)^2
      possibleImages : Set (MultiradialCarrier D) -- union over Ind1,Ind2,Ind3
      hull : Set (MultiradialCarrier D) := holomorphicHull possibleImages

    noncomputable def thetaPilotLogVolume (P : ThetaPilotData D) : WithTop Real :=
      processionNormalizedLogVolume P.hull

    structure QPilotData (D) where
      bad : Finset (FinitePlace D.F)
      logQ : Real := sum_v weight_v * ord_v(q_v) * log residueChar(v)
      qPilotLogVolume : Real := -|log q|

    def Cor312Faithful (P : ThetaPilotData D) (Q : QPilotData D) : Prop :=
      thetaPilotLogVolume P != +inf /\
      qPilotLogVolume Q <= thetaPilotLogVolume P

    theorem cor312_faithful_of_objects ... : Cor312Faithful P Q

关键点：thetaPilotLogVolume 必须是 possibleImages 的 holomorphicHull 的 procession-normalized log-volume；
thetaValue 必须用 2*l-th root 的 (j)^2 次幂；normalization 必须包含 j^2 average（LANA 参考写法 sFactor(nC)）。

## 6. 审计结论

- 现有 StepXIContract / Cor312Conclusion 不是 paper Cor 3.12：过弱在对象/2l roots/Ind/hull/average/finiteness/C_Theta，过强在 targetSigned 空转。
- Mzk1QPilotR4Stage5AlignActual 与 Mzk1Step3115ComparisonActual 的 qTheta/step3115 结果不得作为 Cor 3.12 证据；必须重定义为独立 Theta-pilot hull readout。
- 我们的 Cor312ToABCBridgeInterface 的真内容是 hcomp 两条 IUT IV 比较（height_le_normalizedRegionVolume, regionVolume_le_normalizedWeight），它们是显式 named gap；不能用 q<=target 充数。


## 7. O4/O5 对象规格（A499：先把对象构造完）

本节只登记 Lean 定义/结构签名与实际构造状态；不接线、不把对象换成 Prop 字段。

### O4. D-scaling `dsc`（Theta^{j^2} 缩放）

已有真实对象（非 Prop 字段）:

- `LeanFormal/IUT/IUTII/Theta/ThetaLinkAssembly.lean`
  - `sourceEvaluationOrbit (u : U →* G) (q : G) (mu : Subgroup U) (n : Nat) : Set (unitGeneratedSubmonoid u q)`
  - `targetEvaluationOrbit (v : V →* H) (theta : H) (nu : Subgroup V) (n : Nat) : Set (unitGeneratedSubmonoid v theta)`
  - `sourceSquaredLabelOrbit (mu : Subgroup U) (j : Int) : Set (unitGeneratedSubmonoid u q)`
  - `targetSquaredLabelOrbit (nu : Subgroup V) (j : Int) : Set (unitGeneratedSubmonoid v theta)`
  - `thetaLink (e : U ≃* V) : unitGeneratedSubmonoid u q ≃* unitGeneratedSubmonoid v theta`
  - 定理 `thetaLink_image_sourceSquaredLabelOrbit` : `thetaLink e` 的像把 `mu * qbar^(j^2)` 送到 `nu * Theta^(j^2)`.
  状态: 真实代数构造（幂零/单位轨道与链接映射），但作用在 `unitGeneratedSubmonoid` 上，不是 literal hull 上的 `dsc` 映射。

- `LeanFormal/IUT/IUTII/Theta/ConcreteSourceEtaleThetaBridge.lean`
  - `thetaScale (l : PrimeGeFive) (j : SignedLabel l.value) : Real := (theater l).thetaPacket.scale j`
  - `thetaLogScale`, `thetaLogVolume`, `AlgebraicFiniteThetaLevel`
  - `theta_scale_eq_real_value : thetaScale l j = realThetaValue gaussianFiveThetaQ j.1`
  状态: 真实有限 Gaussian theta 包对象；`j^2` 指数见 `SourceLabelWeightedDiagonal.labelWeight`/`realThetaValue_eq_unit_pow`，是有限模型，不是 paper 全 literal Θ-pilot 对象。

- `LeanFormal/IUT/IUTIII/Theorem311/SourceLabelWeightedDiagonal.lean`
  - `labelWeight (j : SignedLabel l) : Nat`（Gaussian 权重 `j^2`）
  - `realThetaValue_eq_unit_pow : realThetaValue q j = q ^ labelWeight j`
  状态: 真实 `q^(j^2)` 代数对角对象；可作为 dsc 的指数/权重来源。

- `LeanFormal/IUT/IUTIII/Theorem311/SourceDThetaConstruction.lean`
  - `structure DColumnStage (n : Int) (k : Nat) where source : Fin (k+1) → I.family.index; strip : ...; link : ...`
  - `def dColumnStage (n : Int) (k : Nat) : I.DColumnStage n k`
  - `structure DColumnInclusion (n : Int) {k r : Nat} (h : k ≤ r) where map : ...; component : ...`
  - `dColumnStage_source/strip/link`, `dColumnStage_link_refl/symm/trans`
  状态: 真实 D fixed-column 对象（D-strip 列与列包含），**不是 dsc scaling action**；可作为 dsc 的 D-side 载体。

缺少的 O4 对象（从已有真实数据构造，不能用 Prop 字段代替）:

```lean
structure DScaling (l : PrimeGeFive) where
  thetaValue : SignedLabel l.value -> Real
  thetaValue_eq : forall j, thetaValue j = thetaScale l j
  exponent : SignedLabel l.value -> Nat
  exponent_eq : forall j, exponent j = labelWeight j
```

以及 paper 的 literal 作用: 对每个 `j`，`dsc` 把 q-bar 的 `mu_(2l)`-orbit 送到 `qbar^(j^2)`-orbit，再在 `unitGeneratedSubmonoid` 上由 `thetaLink e` 同步到 Theta 侧。当前 `thetaLink_image_sourceSquaredLabelOrbit` 已给出这个同步，但尚未打包成 `DScaling` 结构，也尚未作用到 literal hull。

### O5. Ind1/Ind2/Ind3 indeterminacy objects

- `LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind1Reduction.lean`
  - `def Ind1Setoid (I : Input Label Choice) : Setoid Choice`（orbit setoid）
  - `def ind1QuotientMap (I) : Choice -> Quotient (Ind1Setoid I)`
  - `def ind1QuotientLift (I) : Quotient (Ind1Setoid I) -> IndeterminacyQuotient I`
  - `structure Ind1DescentData (I : Input Label Choice)`
  - `def ind1DescentDataCanonical (I) : Ind1DescentData I`
  - `theorem ind1DescentData_descends`
  状态: 真实商集/下降对象；载体是有限模型 `Input Label Choice`，不是 paper literal Hodge theater 的 Ind1 action。

- `LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind2Reduction.lean`
  - `structure Ind2AlienLink (LabelNative LabelAlien : Type u) (Native Alien : Type v) [AddGroup LabelNative] [AddGroup LabelAlien] where
      nativeCore : Core LabelNative Native; alienCore : Core LabelAlien Alien;
      labelCopyMap : LabelNative -> LabelAlien; linkMap : Native -> Alien;
      linkMap_ind1 : ...; linkMap_ind2 : ...`
  - `def secondLinkDescent`, `theorem secondLinkDescent_eq_lift`, `secondLinkDescent_unique`
  - `structure` 的 fields 是实际函数与交换律，不是 Prop 占位。
  状态: 真实 mutually-alien copies 对象；不是 paper 全 Ind2 算法。

- `LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind3Reduction.lean`
  - `structure PossibleImage (β : Type v) [Preorder β] where carrier : Set β`
  - `def lowerClosure`, `theorem lowerClosure_idem`, `IsLowerClosed`
  - `def iUnion`, `def SurjectionCovers`, `structure UpperSemiCorrespondence`/`IsUpperSemi`
  - `theorem isUpperSemi`
  状态: 真实 upper-semi possible images 的集合层对象；尚未与 Theta hull/Ind1/Ind2 组合成 paper 的 Ind3 作用。

### 对象状态汇总（O4/O5）

| 对象 | Lean 名称 | 构造 | 是否 paper-literal |
|---|---|---|---|
| Theta^{j^2} 对角/权重 | `thetaScale`, `labelWeight`, `realThetaValue_eq_unit_pow` | 真实 | 有限模型 |
| squared-label orbit/link | `sourceSquaredLabelOrbit`, `targetSquaredLabelOrbit`, `thetaLink` | 真实 | 代数层 |
| D column stage | `DColumnStage`, `dColumnStage`, `DColumnInclusion` | 真实 | D-side 载体 |
| dsc 单对象 | `DScaling` (草案) | 缺打包 | 缺 literal action |
| Ind1 | `Ind1Setoid`, `ind1QuotientMap/Lift`, `Ind1DescentData` | 真实 | 有限模型 |
| Ind2 | `Ind2AlienLink`, `secondLinkDescent` | 真实 | 有限模型 |
| Ind3 | `PossibleImage`, `lowerClosure`, `IsUpperSemi` | 真实 | 集合层, 未接 hull |

结论: O4/O5 已有真实可复用构造，但 paper-literal 单对象（`DScaling` action + literal Ind1/2/3 on theta hull）仍缺；不得把 `StepXIContract` 的 Prop 字段或 `qTheta` 读法当作这些对象。

