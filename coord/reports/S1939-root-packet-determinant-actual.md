# S1939：actual root packet determinant（Corollary 3.12 的实际 determinant）

日期：2026-11-01。任务：在 D:\lean 中从**实际 root packet**（rootNormedThetaValueInL，等价地 rootNormedElement / singleLambda）构造 SignedHullLogActual，使 S1904 procession average = s1915A0 T，或给出精确第一 missing；不得 fake log-volume。

## 结论（先给结果）

**在没有新 source 输入时，actual root packet 的自然 determinant 使 procession average 精确等于 S1915 的 unclipped closed form，而不是 1/5 模型的 log 5 公式；要让它同时是合法 hull packet，所需的唯一输入是一个具体的实不等式。**

- 已证（无条件）：'s1939_average_eq_closedForm'
  'average = 1 + S = s1915ClosedForm T'，其中
  'S = sum_b [K_b:Q_p] * log||root_b||'，'root_b = rootNormedElement T b'。
  这是 S1928 所指的 actual root packet 关系，不再出现 log 5。
- 已证：hull packet 合法（每个 scale >= 1）**当且仅当**
  '(l*)^2 * |S| <= M'，其中 'l*=(l-1)/2'，'M=l(l+1)/12'（S694 的 j-normalization）。
  这是精确第一 missing（'S1939FirstMissing'）。
- 在该 bound 下：'average = s1915A0 T'（'s1939_average_eq_a0'），
  'S1904ProcessionBridge (s1902ActualThetaHull T) s1939Determinant' 成立
  （'s1939_bridge'），构造出 'OrigXiFPaperSignedHullData'（'s1939Datum'），
  并由 S1880 得 Corollary 3.12 不等式
  '-|log q| <= OrigXiFSignedThetaHullLogVolume (s1939Datum T h)'（'s1939_cor312'）。
- 无条件恒等式与 bound 的等价性：'s1939_exists_bridge_iff_hullScaleBound'
  说明，具有这些 actual packet/procession 字段的 determinant 满足 S1904 bridge
  **iff** bound 成立。所以 "missing" 不是新的 transcendence 命题，也不是 log 5 等式，
  而是 actual local qVFamily 数据的一个具体不等式。

## 构造（不 fake）

对每个坏地方 b、每个 signed label j：

    s1939RootLog b j      = log ||rootNormedThetaValueInL T b j||
    s1939LabelLog j       = sum_b [K_b:Q_p] * s1939RootLog b j
    s1939BadLog T         = sum_b [K_b:Q_p] * log ||rootNormedElement T b||
    M                     = l(l+1)/12
    s1939RootLogScale j   = 1 + s1939LabelLog j / M
    hullPacket.scale j    = exp (s1939RootLogScale j)

procession：正 label j=1,...,l* 上权重 '1/l*'，0 与负 label 上权重 0。
reference packet 为单位 packet；tensor power = 1。

关键恒等式（S201/S1928）：

    ||root_b^(j^2)|| = ||root_b||^(j^2)
    s1939LabelLog j = j^2 * s1939BadLog T

因此 's1939RootLogScale j = 1 + j^2 S/M'。由
'sum_{j=1}^{l*} j^2 = l* * M'（S1930 的 's1930_sum_sq_paperLabel'，即 'l(l^2-1)/24 = l*·l(l+1)/12'），

    average = (1/l*) sum_{j=1}^{l*} (1 + j^2 S/M)
            = 1 + S
            = s1915ClosedForm T.

'1' 是 paper packet normalization 的 archimedean e-normalization（Remark 3.9.5(i)；
'j=0' 的实际 theta value 为 1，'s1939RootLogScale_zero' 给出 scale = e）；
'M' 是 paper 的 j-normalization（S694：l* 类、权重 1/l* 的 j^2 平均值）。

## 精确第一 missing

    S1939FirstMissing T  :=  (l*)^2 * |S| <= M
    <=>  forall j, 1 <= (s1939RootPacket T).scale j          (s1939FirstMissing_iff_scales)
    <=>  (l*)^2 * |(1/(2l)) * sum_b d_b * log||q_b||| <= M   (s1939FirstMissing_iff_qNorms)

其中 'q_b = sourceRootQUnit T b'。证明使用的唯一方向事实是：正 label 中
'j^2 <= (l*)^2'，且 'S<0'（'s1928_local_sum_neg'）。bound 成立时 '|S|<1'，
故 's1915ClosedForm = 1+S > 0'，'s1915A0 = 1+S'。

区分两个不同强度：

- 's1939_average_eq_a0_iff'（无条件）：'average = a0' 当且仅当 '|S| <= 1'。
  这是 S1915 的 ENNReal clipping（否则 a0 = 0）。
- 's1939_hullScaleBound_iff'（结构要求）：determinant 是合法 SignedHullLogActual
  当且仅当 '(l*)^2|S| <= M'，严格强于 '|S| <= 1'。

## determinant 与 3.12

's1939Determinant T h'（h : bound）：

- 'hullPacket = s1939RootPacket T'（actual root packet）
- 'referencePacket = 1'，'tensorPower = 1'
- 'procession = s1939Procession T'（paper l* weights）
- 'hullLogVolume = l + (l-1)S = l*a0 + |S|'
  （'s1939Determinant_hullLogVolume'、's1939Determinant_hullLogVolume_eq_a0'）
- 'procession.average = a0'（'s1939_average_eq_a0'）
- S1904 bridge（'s1939_bridge'）

's1939Datum T h : OrigXiFPaperSignedHullData (S1902Carrier T) l'，其
'signedLogVolume = -a0'（'s1939Datum_signedLogVolume'），
's1939_cor312' 给出 '-|log q| <= -|log Theta|'。

## 边界（如实）

- bound '(l*)^2|S| <= M' **未证明**；当前 SourceNativeInitialThetaData 输入只给
  '||q_b|| <= 1'（S664），没有下界，因此不能从现有接口推出。缺的不是 log 5 / Lindemann–Weierstrass，
  而是 actual local qVFamily data 的实不等式。
- 因此 3.12 在本包中是 **conditional on the hull-scale bound**；不是无条件闭合。
- bound 失败时，自然的 actual root packet determinant 不是 SignedHullLogActual
  （某 scale < 1）；'s1939_exists_bridge_iff_hullScaleBound' 精确表达了这一点。
- 未运行：全 Project 构建、comparator、独立审查；未改 coord/STATE、coord/queue、AUDIT_LEDGER。

## 证据

- 源文件：'tmp/sheaf/xif/paper/S1939RootPacketDeterminantActual.lean'
  - 33232 bytes；SHA256 '3DDEAE5CFE2DD49BCA7DDB52453BEEA3FBE4EC057B9ED0FA4306F997DE312BD8'
  - 'lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1939RootPacketDeterminantActual.olean tmp/sheaf/xif/paper/S1939RootPacketDeterminantActual.lean'
  - EXIT=0，无 error，无 sorry/admit/axiom/True/PUnit；未使用 fake log-volume。
- olean：935160 bytes；SHA256 'B1628F0BA74587268838397FB1EA8951741BC56192F22C9BA0DB6FE04DB05BCE'
- '#print axioms'：所有主定理仅 '[propext, Classical.choice, Quot.sound]'
  （s1939LabelLog_eq, s1939_average_eq_closedForm, s1939_absBadLog_lt_one,
  s1939_closedForm_pos, s1939_average_eq_a0, s1939_average_eq_a0_iff,
  s1939_average_eq_a0_of_abs_le_one, s1939_hull_scales_ge_one,
  s1939_hullScaleBound_of_scales, s1939_hullScaleBound_iff, s1939Determinant,
  s1939Determinant_hullLogVolume, s1939Determinant_hullLogVolume_eq_a0,
  s1939_bridge, s1939Datum, s1939Datum_average, s1939Datum_signedLogVolume,
  s1939_cor312, s1939_ray, s1939_exists_bridge_iff_hullScaleBound,
  s1939FirstMissing_iff_exists_bridge, s1939FirstMissing_iff_qNorms,
  s1939RootLogScale_eq, s1939RootLogScale_zero, s1939RootPacket_scale_zero,
  s1939Determinant_hullPacket, s1939Determinant_procession,
  s1939_nonempty_datum_of_bound）。
- Consumer：'tmp/sheaf/xif/paper/_S1939Consumer.lean' import 该 olean，
  EXIT=0，re-derive bridge / average / Cor 3.12 / 第一 missing 等价式；axioms trio。

## 复用

- S1928：'s1928RootNorm', 's1928RootNorm_pow', 's1928_log_rootNorm',
  's1928_closedForm_eq', 's1928_local_sum_neg', 's1928_average_pos' 等；
- S1930：'s1930PositiveLabel', 's1930PositiveFilter_sum_eq',
  's1930_sum_sq_paperLabel', 's1930_gaussSum_eq', 's1930ZeroLabel' 等；
- S1915：'s1915ClosedForm', 's1915A0', 's1915_a0_eq_closedForm',
  's1915_bridge_iff_average_eq_a0'；
- S1902 's1902ActualThetaHull'，S1904 'S1904ProcessionBridge'，
  S1880 's1880_xiF_inequality_abs'。

## 下一步（给集成者）

1. 若 source 数据能证明 '(l*)^2|S| <= M'（例如 q_v 的显式高度/次数上界），
   则 's1939Determinant' 无条件、Cor 3.12 在该对象上闭合；把它作为新 source 输入登记，
   而不是把它藏进 determinant。
2. 若希望去掉该 bound，需要改变 paper l* procession 的 normalization（例如数据依赖的
   M'），但这会被视为 normalization engineering；本包不做。