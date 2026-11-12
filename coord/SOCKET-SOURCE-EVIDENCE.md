# SOCKET-SOURCE-EVIDENCE — FiniteCertificateLinkEvidenceWiring 的 hq_align / hth（A486 只读调查）

日期: 2026-11-11。范围: LeanFormal/ 全树、tmp/sheaf/xif/paper 可见资产、coord/repo-route-index-data.json、dag 声明索引抽查。
被调查对象: `LeanFormal/IUT/IUTIII/Corollary312/StepXI/FiniteCertificateLinkEvidenceWiring.lean`
- `hq_align : certificate.qSigned ≤ absoluteDegreeNormalizedLowerSignedLog S.selectedLowerPlaces S.parameters`
- `hth : S.thetaSigned ≤ certificate.thetaSigned`

## 每 socket 一行结论

| socket | 已有证据 (file:decl) | 缺什么 |
|---|---|---|
| hq_align | `LeanFormal/IUT/IUTIII/Corollary312/StepXI/ContractSourceReduction.lean:183` `StepXIFiniteCertificate.ofAbsoluteDegreeNormalizedSignedLog_qSigned`（`[simp] rfl`：凡用同一 `selectedLowerPlaces/parameters` 构造的证书，`certificate.qSigned` 定义性地等于 `absoluteDegreeNormalizedLowerSignedLog ...`，故 socket 为 `le_rfl`）；源侧 q-log 对象链：`tmp/sheaf/xif/paper/S2981SignedQPilotActual.lean:154` `sourceQPilotSignedLog`、`ConcreteGlobalPilotDataActual.lean:72` `concreteQPilotLogVolume_eq_sourceQPilotSignedLog`、`ConcreteQPilotLogIdentificationActual.lean:23` `ConcreteSourceQIdentification`、`globalQPilotSignedLog_eq_sourceQPilotSignedLog` | 对**通用**证书没有 `hq_align` 证明（socket 只在"证书由同一 places/parameters 构造"时是定义性的，这是跨卡对齐本身）；仓库无 `absoluteDegreeNormalizedLowerSignedLog = sourceQPilotSignedLog / concreteQPilotLogVolume` 的等式定理（多轮 grep 0 命中）；`SourceColumnCarrierIdentification`（LeanFormal/IUT/IUTIII/Corollary312/StepXI/）只给 ind1/2/3 column realization，不含标量对齐 |
| hth | `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardAMPLThetaBoundSupply.lean:161` `CardAMPLThetaBoundSupply.certificate_thetaSigned`（`[simp] rfl`：AMPL 证书 `thetaSigned = S.theta`）；AMPL 路线的 socket 形态 `S.thetaSigned ≤ S_ampl.theta` 见 `FiniteCertificateLinkEvidenceWiring.lean:132/152`；源侧 theta 体积对象：`LeanFormal/IUT/IUTII/Theta/ConcreteSourceEtaleThetaBridge.lean:56/59/62` `thetaScale/thetaLogScale/thetaLogVolume`、paper 桥 `tmp/sheaf/xif/paper/EtTh07ConcreteBridgeActual.lean:72` `etThThetaLogVolume`、`ConcreteSourceHistoryLinkBridge.lean` `packet_volume/sourceHistory_scale_product` 等 | 无 `S.thetaSigned ≤ certificate.thetaSigned` 的一般定理；也无把 QCMP `S.thetaSigned` 与源侧 `thetaLogVolume/etThThetaLogVolume` 或 AMPL `S.theta` 对齐的源级定理（QCMP 只在各构造中有定义性到 q-log 的等式，如 `QCMPComparisonSupply.ofCanonicalCollapse`，非跨卡 socket） |

## 补充事实

- `LeanFormal/IUT/IUTIII/Corollary312/StepXI/FiniteAlignmentSocketInstance.lean` 在具体有限测试载体（Q(i) at 5，canonical collapse）上把**两个 socket 都化为 `le_rfl`**，从而完整 inhabits `linkEvidenceOfQCMPWithIPL` 并到达 `Cor312Conclusion`；该文件自述"finite test-carrier instance only … NOT a source instantiation，non-degenerate source-level alignment identification remains open"，不能当作源级证据。
- `Source*Alignment*` 系列（`SourceK1K2ComparisonAlignment.lean`、`SourceDefinition31DualContractAlignment.lean`、`SourceTateParameterAlignment.lean`、`SourcePsiPunctureAlignmentFromCurve.lean` 等）均是不同对象（Ind3 K1K2、scheme-side 3.1、Tate 参数、puncture）的对齐，不是 hq_align/hth 这两个标量 socket。
- `SourcePolyIsoTransportDischarge.lean` 提供 route/Iso 传输与 `trivialSupply`（IPL 侧），也不含这两个标量对齐。
- 结论：两个 socket 都是**源级真正缺失**（已有"构造内定义性"证据 + 源侧对象，缺跨卡等式/不等式定理），与 wiring 文件自述一致。
