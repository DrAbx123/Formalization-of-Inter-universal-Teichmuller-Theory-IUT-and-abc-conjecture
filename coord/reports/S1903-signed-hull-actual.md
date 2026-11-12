# S1903：实际 SignedHullLogActual（逆 theta 的 det^{tensor M} 根 packet）

日期：2026-11-01。范围：把 `_S1903Probe2.lean` 的实际构造整理为生产文件
`tmp/sheaf/xif/paper/S1903SignedHullActual.lean`，供 S1905 组装
（`OrigXiFPaperSignedHullData.determinant`）。

## 结论

- 实际 determinant 已构造并通过 kernel 检查：
  `s1903ActualDeterminant (l : PrimeGeFive) : SignedHullLogActual (SignedLabel l.value)`。
- 无 `sorry`/`admit`/`axiom` 声明；19 个 `#print axioms` 探针全部只有
  `[propext, Classical.choice, Quot.sound]`。
- 编译 `EXIT=0`（无 warning），olean 已落到 lake 搜索路径，
  consumer probe 以 `import tmp.sheaf.xif.paper.S1903SignedHullActual` 通过。

## 构造（实际数据，不是 fake）

- `s1903TensorPower l = card(SignedLabel l.value) ^ 3`；
- `s1903RootHullPacket l M`：`scale j = exp (-(thetaLogScale l j) / M)`，
  即实际 theta packet 的逆的 M 次根；scales ≥ 1 由实际 `thetaScale <= 1` 得到；
- `s1903RootProcession l M`：weights `1/card`（总和 1），values
  `-(thetaLogScale l j)/M`，且已证 values = log(root scale)；
- reference packet 直接取 `HullPacketActual.referencePacket l`，复用已证
  `HullPacketActual.referencePacket_logVolume_zero`；
- `Data l → SignedHullLogActual` 的包装与 `HullPacketActual.toSignedHullLogActual` 同形，
  `sourceData` 取 M = card^3。

## 实际 log-volume 恒等式（已证）

- `hullLogVolume = M * packetLogVolume(root packet) = -thetaLogVolume l`
- `signedHullLogVolume = thetaLogVolume l <= 0`
- `processionNormalizedLogVolume = -thetaLogVolume l / (M * card)`
- `packetDet(root packet) = exp (-thetaLogVolume l / M)`
- determinant 形式：`hullLogVolume = M * log (packetDet hullPacket)`

这些量都是实际 packet 的 `packetLogVolume`/`packetDet`，没有 fake log-volume。

## “调用 HullPacketActual.toSignedHullLogActual” 的精确回答

该字面路由在 actual source 上不可用，且不是“未证明”而是假：
`HullPacketActual.SourceFields l` 要求 `forall j, 1 <= thetaScale l j`，
而 `thetaScale l j = (1/5)^(j^2) <= 1`，在 `j = 1` 处等于 `1/5`。
本文件证明：

- `s1903_thetaScales_ge_one_false : not (forall j, 1 <= thetaScale l j)`；
- `s1903HullPacketActualData_empty : IsEmpty (HullPacketActual.Data l)`；
- `s1903_hullPacketActual_shape`：记录 `HullPacketActual.toSignedHullLogActual l D` 的形状
  （对假设中的 `D : HullPacketActual.Data l`；没有断言空类型的 inhabitant）。

因此实际 determinant 必须用逆 theta 的根 packet；本文件即该构造。

## 证据

- Lean：`tmp/sheaf/xif/paper/S1903SignedHullActual.lean`，580 行，25813 字节，
  SHA256 `92EC9B7FD1F8A63FF73801FF544F1344424F77DA3A856645AFAB90146D9659C9`。
- 编译：`lake env lean -j1 -R D:/lean tmp/sheaf/xif/paper/S1903SignedHullActual.lean`，
  EXIT=0，无 warning/error；`S1903_verify.log` 只含 19 条 axiom 结果。
- olean：`.lake/build/lib/lean/tmp/sheaf/xif/paper/S1903SignedHullActual.olean`，
  352512 字节，SHA256 `CB2CBD865ED3B0BE529B950EC57CC13396AD528C693734451ADC2A5948C8C476`
  （与独立复编 `_S1903Verify.olean` 字节一致，再删除了临时 olean）。
- consumer probe：`tmp/sheaf/xif/paper/_S1903ConsumerProbe.lean`，EXIT=0；
  S1904 的 `S1904FirstMissing`、`s1904ProcessionAverage`、
  `s1904_processionAverage_nonneg` 均接受 `s1903ActualDeterminant l`。

## 边界与并发说明

- S1904 procession bridge 未断言（真缺口，见 S1904/S1915 报告）；本文件只供 determinant 字段。
- `S1917AverageLeOneActual` 独立构造了同一 determinant 以证 `procession.average <= 1`，
  存在重复；S1905 组装时应二选一或交叉引用。
- 文件 §5（`ProcessionNormalizedLogVolumeActual` 接口，含额外 import 与
  `s1903ProcessionNormalized_*`）由并发 worker 于 14:43:40 追加；
  本包验证的是整文件 580 行版本，未修改/覆盖其内容。
- 未修改 `HullPacketActual.lean` 与 `S1905Unconditional312Actual.lean`；
  未运行全 Project 构建、comparator 或独立人工审查。
