# IUT 论文路线（以仓库原文为准）

日期：2026-11-09。本文覆盖之前把仓库 interface 当路线的错误描述；活动路线以
`papers/motizuki_corpus/text/` 的望月原文与补充材料为准。

## 构造纪律（2026-11-09 追加）

Stage 1–5 只用于审计定位，不是构造模板。不要先造 BPS/etHT/multiradial
的具名空壳再回头改；直接从已有实际载体（MultiradialProcession、IPLAPT、
S1204/S1215/S1300/S1385 等）证明论文中的实际箭头/不等式。

判断标准：一个 def 若只是把论文对象写成带任意 Prop 字段的结构，先不做；
优先证已有载体的具体性质、兼容性、比较。空壳结构不算进展。

S3128 prestack mapId：若 `S3128ZMod2QuotientSheafObj` 缺 mapPoint naturality，
不要为 mapId 临时加字段；标记为 [FrdI-II] 基础设施缺口，转回论文实际对象。

## 0. 原文依据

- `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt:10324-10353`
  - Corollary 3.12: `−|log(Θ)| ≥ −|log(q)|`，即 `CΘ ≥ −1`。
- `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt:1255-1385`
  - Theorem 1.10: 由 Cor 3.12 的 `CΘ ≥ −1` 得显式 log-volume 不等式。
- `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt:2329-2332`
  - §2: Theorem 1.10 + [GenEll] ⇒ ABC / Vojta（Cor 2.3）。
- `papers/motizuki_corpus/text/Formalization of IUT (2026-04).txt:116-125`
  - 形式化 Stage 1–5。
- `papers/motizuki_corpus/text/Formalization of IUT (2026-04).txt:443-621`
  - §4: BPS → multiradial representation → hull+det；
    descent (dsc) / APT / IPL / SHE；
    `3.11.5 ⇒ 3.12` 是第四三角形。
- `papers/motizuki_corpus/text/Explicit estimates in IUTeich.txt:1-56`
  - Stage 5 数值/effective 版本。

## 1. 望月 Stage 1–5

```text
Stage 1 : [IUTchIII] Theorem 3.11 ⇒ Corollary 3.12
Stage 2 : Proof of [IUTchIII] Theorem 3.11 modulo [IUTchI-II]
Stage 3 : [IUTchI-II] modulo earlier results (1995-2015)
          on anabelian geometry/Frobenioids/theta functions, etc.
Stage 4 : Earlier results (1995-2015):
          [pGC], [GeoAn], [AbsAnb], [NCBel], [AbSc], [SemiAn],
          [QuCnf], [CbGC], [Confi], [FrdI-II], [EtTh], [GenEll],
          [NodNon], [AbsTopI-III]
Stage 5 : Numerical aspects ([IUTchIV], [ExpEst])
```

当前形式化处在 Stage 1 早期 skeletal 部分（原文 2026-04，:125）。

## 2. §4 四三角形（Stage 1 的实际内容）

```text
BPS
  --multiradial algorithm--> multiradial representation
  --hull+det--> multiradial representation + hull + det

descent (dsc)
APT
IPL
SHE

Thm. 3.11:
  (dsc) APT + IPL
  => 1st/2nd/3rd triangle
  => "Thm. 3.11.5"
  (hull+det) ∘ (dsc) SHE + IPL
  => 4th triangle
  => Cor. 3.12:
       comparison of q-pilot and Θ-pilot
```

“3.11.5” 不是原文编号；是形式化重组：把 hull+det 从 3.12 移到 3.11.5，
使 3.11.5⇒3.12 专注于 simultaneous comparison。

## 3. 最终 ABC 路线

```text
IUT I: initial Θ-data / Hodge theater
IUT II: log-shell / log-volume / q-pilot / Θ-pilot
IUT III: Theorem 3.11
         -> multiradial representation
         -> Cor 3.12 (CΘ ≥ -1)
IUT IV: Theorem 1.10 explicit log-volume estimate
IUT IV §2: Theorem 1.10 + [GenEll] -> ABC / Vojta
```

## 4. 禁止当路线图的东西

以下都是仓库 interface，不是论文路线，不得当 milestone：

```text
ABCFrontier
Cor312ToABCBridgeInterface
FrontierHeightComparisonClause
FrontierRegionComparisonClause
cor312Gap1_*
cor312Gap2_*
```

`Cor312ToABCBridgeInterface.lean:98-100` 明确写 carrier 是 named interface，
不是 literal paper inductive system。`ABCFrontier ↔ ABCConjecture`，与 ABC 等强，
把它当路线等于把“还差 ABC”包装成“还差 F4/F5”。

## 5. 当前 actual 的作用映射

| actual | 论文位置 | 下游 |
|---|---|---|
| tensor_char / C3 block char / S2733 scaling | IUT II log-shell / log-volume | 需接 Θ-pilot/q-pilot log-volume |
| q-binomial / Jacobi aligned identity / aligned expansions | [EtTh] / Θ-pilot 的 theta 展开 | 需接 étale theta / Θ-pilot |
| G2/G3 / S3127Cover equivalence | Stage 4 anabelian/Galois 侧 | 需接 fiber functor / etHT/BPS |
| OfH functor / CanonicalHEnd | Frobenioid/基变换基础设施 | 需接 [FrdI-II] 的 pseudofunctor |
| S3123LeftExplicit / UnitComp / MapId | fiber functor 宿主 | 需接 S3123FiberEquivalence |
| S3119 AddValuation / ordFrac | function field / height 侧 | 需接 height comparison |

## 6. 当前优先顺序

1. Stage 1 的对象：etHT / BPS / multiradial representation / descent / APT / IPL / SHE。
2. `3.11.5 ⇒ 3.12`：q-pilot 与 Θ-pilot 的 simultaneous comparison。
3. Cor 3.12: `−|log(Θ)| ≥ −|log(q)|`。
4. IUT IV Theorem 1.10 显式估计。
5. Stage 5: Explicit estimates 的 effective 版本。
6. ABC / Vojta。

## 7. 纪律

- 每个 actual 必须能回答：它在 IUT 哪一 stage、哪个对象/不等式？
- 不能回答的，标为“孤岛”，不算主线进展。
- 不引入新的命名 gap 当进展；不把 interface 等价当路线。
- 所有编译走 `tools/build_guard.ps1`；长编译交 subagent；fresh olean + axioms trio 才算 citable。
