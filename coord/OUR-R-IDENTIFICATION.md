# OUR-R-IDENTIFICATION — 我们的 R 与 sourceSignedHullLogVolume / -|log Θ| 的识别 (A1123)

| field | value |
|---|---|
| 目录 | `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/`（52 个 .lean，**全部 olean=True**） |
| 结论 | 现有 stack 已提供 `-|log Θ|` 的 signed carrier（`sourceSignedHullLogVolume`）、符号转换律、xi-f 比较谓词、C_Θ transfer（条件于 `|log q| = -qSigned`）。**可用**这些做我们 R 的识别/转换；**缺**的是我们的 C3 Haar 区域 ↔ `sourceHolomorphicHull` 的桥，以及 `qSigned` 的识别（现有定理里是显式假设，未证）。 |

## 1. 三个文件的关键定理（oleans 均 True）

### 1.1 `CardHullRealSignedLogVolume.lean`
```lean
-- L114-116: -|log(Theta)| 的载体（corpus III:1051-1053, III:10843-10848）
def sourceSignedHullLogVolume (v) (R : SourceImageRealization v) (n : ThetaPilotCarrier l) : Real :=
  -(I.sourceRealHullVolume v R n)

-- L123-125: -|log(q)| 的载体（corpus III:10847-10848）
def sourceSignedImageLogVolume (v) (R) (n) : Real := -(I.sourceSetVolume v (possibleThetaPilotImageSet v R n)).toReal

-- L129-132 / L135-138: 非正性
theorem sourceSignedHullLogVolume_nonpos : sourceSignedHullLogVolume v R n ≤ 0
theorem sourceSignedImageLogVolume_nonpos : ... ≤ 0

-- L143-148: (xi-d) 恒等（rfl）：signed hull = -log(hull set volume)
theorem sourceSignedHullLogVolume_eq_neg_hullSetVolume :
  sourceSignedHullLogVolume v R n =
    -(I.sourceSetVolume v (I.sourceHolomorphicHull v R n : Set _)).toReal        -- rfl
```
**符号转换律**（green，可直接用）：
```lean
-- L155-168（lower side）：-|logΘ| <= -x  ↔  ofReal x <= sourceHullVolume
theorem sourceSignedHullLogVolume_le_neg_iff (hfin : sourceHullVolume < ⊤) (hx : 0 ≤ x) :
  sourceSignedHullLogVolume v R n ≤ -x ↔ ENNReal.ofReal x ≤ I.sourceHullVolume v R n

-- L176-190（upper side）：-x <= -|logΘ|  ↔  sourceHullVolume <= ofReal x
theorem neg_le_sourceSignedHullLogVolume_iff (hfin) (hx : 0 ≤ x) :
  -x ≤ sourceSignedHullLogVolume v R n ↔ I.sourceHullVolume v R n ≤ ENNReal.ofReal x
```
**(xi-f) 比较谓词**（命名条件，未证）：
```lean
-- L198-200
def SourceXifSignedComparison (v) (R) (n) (qSigned : Real) : Prop :=
  qSigned ≤ I.sourceSignedHullLogVolume v R n
```

### 1.2 `CertificateCThetaTransfer.lean`
```lean
-- L57-63: certificate 链 qSigned <= hull <= thetaSigned
theorem StepXIFiniteCertificate.weighted_average_le_theta : weighted.average <= thetaSigned

-- L73-90: C_Θ transfer，**条件于** |log q| = -qSigned（显式假设 hq）
theorem cTheta_lower_bound_of_finiteCertificate
  (certificate) {q} (hq : |Real.log q| = -certificate.qSigned) {cTheta}
  (hc : certificate.thetaSigned <= cTheta * |Real.log q|) : -1 <= cTheta
```
**注意**：L44-47 明言“No certificate is constructed here for the actual source carrier;
the identification `|log(q)| = -qSigned` is an explicit hypothesis, not asserted”。

### 1.3 `HullDeterminantLogVolumeReduction.lean`
```lean
-- L123: 冻结 spec（det × log-volume 簿记）
structure HullDeterminantLogVolumeFrozenSpec : Prop where ...
theorem hullDeterminantLogVolumeFrozenSpec_holds : HullDeterminantLogVolumeFrozenSpec   -- L153（green）

-- L173-320: matrixLogDet / packetDet / packetLogVolume / tensorPower 的 det 簿记（green）
noncomputable def matrixLogDet; theorem packetDet_pos; packetLogVolume_eq_matrixLogDet;
theorem packetLogVolume_tensorPower; profileArithmeticDegree ...
```
⇒ **det 簿记工具可用**；但它不是到 `-|log Θ|` 的识别。

## 2. 我们的 `RTarget` 与 `-|log Θ|` 的对应

我们的定义（A1122）：
```
RTarget μ θRegion := -Real.log ((μ θRegion).toReal)      -- μ = actualC3LogShellTensorHaar C3
MTarget := ATarget - RTarget,   ATarget := paperQAbsLog l logQ = logQ/(2l)
```
对照：
```
sourceSignedHullLogVolume = -sourceRealHullVolume ≤ 0    （= -|log Θ|，paper 的负值）
我们的 R = RTarget：若 μθ = exp(-|log Θ|) 型，则 RTarget ≈ +|log Θ|（正值幅度）
⇒ 目标识别：sourceSignedHullLogVolume = -RTarget   （即 -|log Θ| = -RTarget）
```
**可用现成**：
```
✓ sourceSignedHullLogVolume_eq_neg_hullSetVolume（rfl 型，给出 -|logΘ| = -log hull set volume）
✓ sourceSignedHullLogVolume_nonpos（符号）
✓ sourceSignedHullLogVolume_le_neg_iff / neg_le_sourceSignedHullLogVolume_iff（signed ↔ ENNReal）
✓ cTheta_lower_bound_of_finiteCertificate（条件 C_Θ transfer；hq 为显式假设）
✓ hullDeterminantLogVolumeFrozenSpec_holds + det/packet 簿记
```
**缺**：
```
✗ GAP-R-IDENT：我们的 μ/C3 θRegion ↔ sourceHolomorphicHull / sourceHullVolume 的桥
   （即 RTarget = -sourceSignedHullLogVolume 或 sourceRealHullVolume = Real.log μθ 的定理）；
   现有 stack 是 I.SourceImageRealization 抽象，不与 S2717/S2807 的 C3 tensor Haar 连接；
✗ GAP-QSIGN：|log q| = -qSigned 的识别（CertificateCThetaTransfer 里是显式假设 hq，未证）；
   对应我们的 A = paperQAbsLog l logQ；
✗ GAP-XIF：SourceXifSignedComparison（xi-f 比较本身）是命名条件，**未推导**；
   它是我们的 variant（qSigned ≤ -|logΘ|）的 source 版；
✗ GAP-C3-HULL：actualC3LogShellTensorRegion 与 sourceHolomorphicHull 的区域对应。
```

## 3. 建议（不新建 target 文件）

1. 将 `Mzk1OurAccurateTargetActual` 的 `RTarget` **解读为** source 层的 `-sourceSignedHullLogVolume`：
   在文档/适配层写 `RTarget_eq_neg_sourceSignedHullLogVolume` 作为**显式 GAP Prop**，
   不在 Lean 中伪造；
2. 用 `sourceSignedHullLogVolume_le_neg_iff` 把我们的 signed 目标翻译成 ENNReal 层的
   `ofReal x ≤ sourceHullVolume`（x = A），这是**现成**的；
3. `cTheta_lower_bound_of_finiteCertificate` 可直接复用于 C_Θ 部分，但必须显式提供 `hq`；
4. det 簿记用 `HullDeterminantLogVolumeReduction` 的 green 定理，不重复构造；
5. 不要在 C3 与 source 抽象之间造新接口，除非先补 GAP-R-IDENT；
   建议把 GAP-R-IDENT 登记到 `coord/CONDITION-LATTICE.md`/`REUSE-AUDIT-ABC.md`。

## 4. 判定汇总

| 项 | 状态 |
|---|---|
| `-|log Θ|` 的 signed carrier | **已有**（sourceSignedHullLogVolume，green） |
| signed ↔ ENNReal 符号转换 | **已有**（两条 iff，green） |
| (xi-f) 比较谓词 | **已有定义**（SourceXifSignedComparison），未证 |
| C_Θ transfer | **已有（条件）**（hq : |log q| = -qSigned 显式假设） |
| det × log-volume 簿记 | **已有**（FrozenSpec + packet det 定理，green） |
| 我们的 RTarget ↔ sourceSignedHullLogVolume | **缺**（GAP-R-IDENT） |
| A ↔ -qSigned | **缺**（GAP-QSIGN） |
| C3 region ↔ sourceHolomorphicHull | **缺**（GAP-C3-HULL） |
| variant 本身（SourceXifSignedComparison） | **未推导**（GAP-XIF；不可假设） |