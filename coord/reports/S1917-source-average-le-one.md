# S1917：实际源 determinant 的 procession average ≤ 1

日期：2026-11-01。任务：S1904 已证 bridge ⇒ average ≤ 1，且 uniform exp2
determinant 使 bridge 假；无条件 3.12 需要实际 S1902/S1880 源 determinant 的
procession average ≤ 1。要求：用算术约束/单位参考包/几何标度证明该界，或给出
精确第一 missing；不得 fake。

## 结论

1. [已证，无条件] 在由实际 theta 尺度构造的源 determinant
   s1917SourceDeterminant l 上，

       (s1917SourceDeterminant l).procession.average ≤ 1

   对所有 l : PrimeGeFive（l ≥ 5）成立（s1917_sourceAverage_le_one）。
   该结论不依赖 bridge、不依赖 theta hull 的 Haar 泛函选择、不依赖
   OrigXiFPaperSignedHullData 的居民。

   进一步，S1903 已建立 canonical 源 determinant 工件
   s1903ActualDeterminant；本包在 §4b 证明它与 S1917 的归一化平均相同，
   并直接得到

       (s1903ActualDeterminant l).procession.average ≤ 1

   （s1917_s1903ActualDeterminant_average_le_one）。因此该界是在实际
   S1903 源 determinant 上，而不是只在 S1917 的独立重写上成立。

2. [已证，否定性发现] 直接把实际 theta packet 当作
   SignedHullLogActual.hullPacket 的“字面”路线不可用：实际源 q = 1/5，故
   thetaScale l j = q^(j^2) ≤ 1；而 SignedHullLogActual 的 hull_scales_ge_one
   要求 ≥ 1。HullPacketActual.SourceFields l 的字段 theta_scales_ge_one 不是
   “尚未证明”，而是假的：

       s1917_literalSourceFields_false : ¬ HullPacketActual.SourceFields l

   因此任何以该字面字段为假设的“源 determinant average”构造都是 vacuous；
   本包不采用该路线。

3. [构造] 实际源 determinant 取实际 theta 尺度的逆包的 M 次根，M = card^3：
   hull scale 为 exp(-log(thetaScale l j)/M)，procession value 为
   -log(thetaScale l j)/M，reference packet 全 1，procession 权重均匀 1/card。
   这是真正的 SignedHullLogActual（所有尺度 ≥ 1，权重非负且总和 1），
   其平均为

       -thetaLogVolume l / (M * card)。

4. [算术界] 由 q = 1/5、j^2 ≤ lStar^2、lStar ≤ card、log 5 ≤ 4，
   得到 -thetaLogVolume l ≤ 4 * card^3。代入 M = card^3 得
   average ≤ 4/card ≤ 4/5 ≤ 1。证明只使用实际有限算术与几何标度 M，
   不使用源 theta 尺度的“假设”上界。

5. [精确第一 missing] 源 determinant 的 average 界已经无条件证出；
   对无条件 3.12 仍缺的精确对象是 S1904 的 procession bridge：

       S1917FirstMissing T :=
         S1904ProcessionBridge T (s1917SourceDeterminant l)

   在 canonical S1903 determinant 上同一缺口写作

       S1917S1903FirstMissing T :=
         S1904ProcessionBridge T (s1903ActualDeterminant l)

   并有 s1917S1903FirstMissing_iff :
   S1917S1903FirstMissing T ↔ S1917FirstMissing T（因两者平均相等）。
   即 thetaHull.haar.logVolume thetaHull.compactHull.hull =
   ENNReal.ofReal (determinant.procession.average)。
   本文件没有断言该等式，也没有构造 OrigXiFPaperSignedHullData 的居民。
   按 S1904 报告的口径，真正的实质缺口仍是“从实际算术 Haar readout 构造
   并识别 hull 值”的恒等式，而不是 determinant average 界。

## 构造细节

- s1917TensorPower l = (Fintype.card (SignedLabel l.value))^3。
- s1917RootHullPacket l M : PositivePacket (SignedLabel l.value)，
  scale j = Real.exp (-(thetaLogScale l j) / M)。
- s1917RootProcession l M : WeightedValues (SignedLabel l.value)，
  value j = -(thetaLogScale l j)/M，weight j = 1/card，weightTotal = 1。
- s1917SourceDeterminant l : SignedHullLogActual (SignedLabel l.value)，
  hullPacket = s1917RootHullPacket l (s1917TensorPower l)，
  referencePacket 全 1，tensorPower = s1917TensorPower l，
  procession = s1917RootProcession l (s1917TensorPower l)。

与 S1903 canonical 工件的对应：

- s1917_s1903ActualDeterminant_average :
  (s1903ActualDeterminant l).procession.average =
  -thetaLogVolume l / ((s1903TensorPower l : Real) * card)。
- s1917_s1903ActualDeterminant_average_eq :
  S1903 与 S1917 两个 determinant 的 procession average 相同。
- s1917_s1903ActualDeterminant_average_le_one :
  (s1903ActualDeterminant l).procession.average ≤ 1。

关键等式：

- s1917SourceDeterminant_average :
  average = -thetaLogVolume l / ((s1917TensorPower l : Real) * card)。
- s1917SourceDeterminant_hullLogVolume :
  hullLogVolume = -thetaLogVolume l。
- s1917SourceDeterminant_signedHullLogVolume :
  signedHullLogVolume = thetaLogVolume l。
- s1917_signedProcession_ge_neg_one :
  -1 ≤ signedProcessionNormalizedLogVolume，
  即 S1880/S1904 侧需要的下界。

## 与 S1902/S1904 的关系

- 使用的 thetaScale/thetaLogScale/thetaLogVolume 是实际
  ConcreteSourceEtaleThetaBridge 的源 packet（S1880/S1902 共用同一
  Gaussian q = 1/5 数据），没有引入自由实数或任意 packet。
- 本包没有 import S1902ActualThetaHullActual。原因：S1902 是 13:25 新落地、
  编译依赖仍在演化的文件；S1904 报告建议下一个包再 import S1902 + S1904。
  本包的 average 界不需要 S1902 hull 的具体 Haar 值；把它与 S1902 的
  a0 = (s1902LogVolume T (s1902Hull T)).toReal 识别，正是 bridge 侧的工作，
  不应通过选 determinant 来绕过。
- 特别地，本包没有断言
  average = a0，也没有断言 bridge；这与 S1904 报告的警告一致。
- S1903SignedHullActual 已作为 canonical 源 determinant 工件存在；本包
  import 它并在 s1903ActualDeterminant 上重述 average 界（§4b），没有
  复制/替换其实义。

## 证据

- Lean：tmp/sheaf/xif/paper/S1917AverageLeOneActual.lean
  - 613 行，26703 字节
  - SHA256：CBEFC54F62042D529346A33E3EB563AF4F04E49365DF3F8F750641B44DA444D9
  - 编译：lake env lean -j1 -R D:\lean -o ... S1917AverageLeOneActual.lean
    EXIT=0，无 warning；共享工作区并发 olean 读失败时重试后通过。
  - olean：.lake/build/lib/lean/tmp/sheaf/xif/paper/S1917AverageLeOneActual.olean
    456264 字节
  - olean SHA256：DDF62AEE2C26A45553EA386823859E608CCA3BB9B64C7900B6F39A8D94FEB3AB
  - #print axioms（文件内 14 个主声明）：均仅
    [propext, Classical.choice, Quot.sound]，无 sorryAx。
- 轻量 import check：tmp/sheaf/xif/paper/_S1917Check.lean EXIT=0，
  #check 输出确认：
    s1917_sourceAverage_le_one (l) :
      (s1917SourceDeterminant l).procession.average ≤ 1
    s1917_s1903ActualDeterminant_average_le_one (l) :
      (s1903ActualDeterminant l).procession.average ≤ 1
    s1917_literalSourceFields_false :
      ¬ HullPacketActual.SourceFields l
    s1917S1903FirstMissing_iff (T) :
      S1917S1903FirstMissing T ↔ S1917FirstMissing T
  并确认 axioms 为 trio。
- 未运行：全 Project 构建、S1902/S1905 联编、comparator 验收、独立人工审查。
  S1902/S1905 的具体联编留给协调层；本包不改 coord/STATE.md、queue.md、
  AUDIT_LEDGER.md（由协调层整合）。

## 边界

- target_accepted = false：average ≤ 1 是必要条件，不是无条件 3.12 本身；
  bridge 仍未构造。
- 没有使用 True/PUnit/sorry/axiom/任意居民；没有把 bridge 或 a0 等式塞进
  假设。
- 字面 theta packet 的 SourceFields 已被证伪，不是“可假设的源字段”；
  这是本包最重要的否定性结论，避免了把 vacuous 构造当作源 determinant。
