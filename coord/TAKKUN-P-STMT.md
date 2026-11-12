# TAKKUN final input (P) vs our hcomp gaps

作者: stepxi。只读审计 Takkun-IUT_LEAN 的 3.11⇒3.12 归约，和我们的 hcomp 两条 IUT IV gap 对照。

## 1. Takkun 的分层归约（exact Lean statements）

### 1.1 PilotVolumeData / cor312（Multiradial/Cor312.lean）

    structure PilotVolumeData where
      Omega : Type u
      [ord : Preorder Omega]
      Gamma : Type v
      [group : Group Gamma]
      [action : MulAction Gamma Omega]
      vol : Omega -> Real
      vol_mono : Monotone vol
      thetaPilot : Omega
      qPilot : Omega
      hull : Omega
      hull_spec : forall g : Gamma, g • thetaPilot <= hull
      containment : exists g : Gamma, qPilot <= g • thetaPilot

    def negLogTheta := vol hull
    def negLogQ := vol qPilot
    theorem cor312 : negLogQ <= negLogTheta

说明: `containment` 是 Thm 3.11 (iii) 的单一空间多radial相容性；Takkun 自己在 TwoSidedLink 中指出单空间 Omega/单 volume 已把“两个 R 的同一化”作为结构前提。

### 1.2 Thm311Transcription / hull_bound（Multiradial/Thm311.lean）

    structure Thm311Transcription (A : ArithmeticData) where
      K : LogKummerCorrespondence
      volR : K.D -> Real
      volR_mono : Monotone volR
      volS : K.F 0 -> Real
      volS_mono : Monotone volS
      kummer0_mono : Monotone (K.kummer 0)
      thetaPilot : K.F 0
      theta_vol : volS thetaPilot = A.arithFactor * (-A.qVol)
      hullR : K.D
      hull_dominates : K.HullDominates thetaPilot hullR
      q_vol : volR (K.kummer 0 thetaPilot) = -A.qVol
      hull_bound : volR hullR <= A.cThetaFormula * A.qVol

    theorem transcription_passes (W : Thm311Transcription A) : A.AdjudicationTest

说明: Thm311 侧把 3.11 的转写归约到唯一 `hull_bound`; 它是 [IUT-IV] Prop 1.1-1.9 的 p 进 log-volume 计算，接收侧 hull 体积上界 `volR hullR <= CTheta * qVol`。

### 1.3 TwoSidedSupply（Multiradial/TwoSidedLink.lean）

    def TwoSidedSupply (factor CTheta : Real) : Prop :=
      exists (T : ThetaLinkComparison.{0,0,0}) (hullR : T.Recv),
        T.volR T.qPilot < 0 /\
        T.volS T.thetaPilot = factor * T.volR T.qPilot /\
        (forall g : T.Gamma, T.link (g • T.thetaPilot) <= hullR) /\
        T.volR hullR <= CTheta * (-(T.volR T.qPilot))

    theorem twoSidedSupply_cTheta_ge_neg_one : TwoSidedSupply factor CTheta -> -1 <= CTheta

说明: TwoSidedLink 分离 Send/Recv 两个 R，最终残余就是 `TwoSidedSupply`; 最后一行是接收侧 hull 体积的 CTheta 上界。

### 1.4 AdjudicationTest（Arithmetic/AdjudicationTest.lean）

    def AdjudicationTest : Prop :=
      exists (T : ThetaLinkComparison.{0,0,0}) (hullR : T.Recv),
        T.volR T.qPilot = -A.qVol /\
        T.volS T.thetaPilot = A.arithFactor * T.volR T.qPilot /\
        (forall g : T.Gamma, T.link (g • T.thetaPilot) <= hullR) /\
        T.volR hullR <= A.cThetaFormula * A.qVol

    theorem adjudication_toSupply : A.AdjudicationTest -> TwoSidedSupply A.arithFactor A.cThetaFormula
    theorem adjudication_implies_height : A.AdjudicationTest -> (1/6)*A.logq <= (1 + 20*A.dmod/A.l)*A.D + 20*(A.estar*A.l + A.eta)

说明: 这是 Takkun 最终可执行输入；`hull_bound` 是其中唯一未由 3.11 机构给出的解析输入。

### 1.5 DisputedCore.MultiradialSupply（更抽象的单空间残余）

    def MultiradialSupply (factor CTheta : Real) : Prop :=
      exists P : PilotVolumeData.{0,0},
        P.vol P.qPilot < 0 /\
        P.vol P.thetaPilot = factor * P.vol P.qPilot /\
        P.negLogTheta <= CTheta * (-P.negLogQ)

    theorem supply_cTheta_ge_neg_one : MultiradialSupply factor CTheta -> -1 <= CTheta

说明: 这是 Cor312.lean 单空间版本的残余；TwoSidedSupply 是它的两 R 分离版。

### 1.6 InitialThetaData/Defs.lean 与 Deferred.lean

- `InitialThetaData.Defs` 定义的是 IUT-I Def 3.1 的初始 Theta 数据：`F`, `E`, `l`, `Fmod`, `Kl`, `coreData` 等，字段是对象数据；不是 3.11⇒3.12 的最终 P。
- `Deferred.lean` 当前是**注释/台账**，说明旧 `opaque` 谓词已由具体定义替换（稳定归约、SL2 像、Galois over Fmod、6-torsion、bad place、KCoreData、valuation section）；文件没有新的 `opaque (P)` 声明。
- 因此 Takkun 的最终输入不在 InitialThetaData，而在 `AdjudicationTest`/`TwoSidedSupply`（以及其单空间残余 `MultiradialSupply`）。

## 2. 我们的 hcomp 两条 gap（Cor312ToABCBridgeInterface）

    structure Cor312EpsilonArithmeticComparison (W : IQHullLogVolumeInterface X) (epsilon : Real) where
      logShellPoint : Nat -> Nat -> Nat -> X
      height_le_normalizedRegionVolume :
        forall a b c, IsABCTriple a b c ->
          Height.logHeight₁ (abcRationalPoint a c) <=
            (1 + epsilon) * (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal
      regionVolume_le_normalizedWeight :
        exists D : Real, forall a b c, IsABCTriple a b c ->
          (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal <=
            (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
              (W.logVolume W.hull).toReal + D

这两条是 IUT IV 侧：高度-区域体积比较、区域体积-算术权重+theta hull 计算；它们是 `Cor312ToABCBridgeInterface` 的显式 named gap。

## 3. 对照结论：不是同一个量

| 项目 | Takkun 最终输入 | 我们 hcomp |
|---|---|---|
| 对象 | Theta-pilot possible images 的接收侧 hull `hullR`; q-pilot `qPilot` | 归一化比较区域 `normalizedComparisonRegion`; rational point / arithmeticWeight |
| 不等式 | `volR hullR <= CTheta * qVol`（或 `<= CTheta*(-volR qPilot)`） | gap1: height <= (1+eps)*regionVolume; gap2: regionVolume <= (1+eps)*weight + hull + D |
| 发送侧/归一化 | 有 `arithFactor = l(l+1)/12` 的发送侧 pin: `volS thetaPilot = arithFactor*(-qVol)` | 无 arithFactor; 用 `(1+epsilon)` 与 arithmeticWeight |
| hull | 单一 Theta-hull `hullR` 的接收侧 log-volume | 比较区域 log-volume 与 W.hull 的 log-volume |
| 结论用途 | `CTheta >= -1` -> thm110 height inequality | 直接组装 ABC height/weight contract |

判定:

1. Takkun `hull_bound` 的 `volR hullR <= CTheta * qVol` 是**单一 Theta-hull 体积上界**；我们的 gap2 是**比较区域体积**相对 arithmeticWeight + W.hull + D 的界。两者都是“hull/区域体积上界”，但不是同一函数、同一归一化、同一对象。
2. Takkun `containment`/`link(g•thetaPilot)<=hullR` 是 q-pilot/Theta-pilot 的像包含；我们的 gap1 是 height 对区域体积的比较。没有同一量关系。
3. Takkun 发送侧有 `arithFactor = l(l+1)/12`（Gauss j^2 average），我们的 hcomp 没有该因子；`(1+epsilon)` 与 `arithFactor` 不等价。
4. Takkun 的 `qVol`/`volR` 是相对 q-pilot 的归一化；我们的 `arithmeticWeight` 是 `log(radical)`，`W.hull` 是 hull 接口；没有已证明的等式连接。
5. 因此 Takkun 的 `AdjudicationTest`/`TwoSidedSupply`/`MultiradialSupply` **不能直接替代或蕴含** hcomp 两条 gap；反过来 hcomp 也不直接给 Takkun 的 `hull_bound`。若要把两者接起来，需要先构造：
   - `hullR = normalizedComparisonRegion` 的 log-volume 等式；
   - `qVol = arithmeticWeight` 的归一化等式；
   - `CTheta` 与 `(1+epsilon)` 的常数吸收/因子关系；
   - 以及 `arithFactor` 的消去/重归一化。
   这些在任何一侧都还没有对象/定理。

## 4. 对 mainline 的建议

- 不要把 Takkun `AdjudicationTest`/`TwoSidedSupply` 登记为 hcomp 或 IUT IV main estimate 的证据；它们只是 Cor 3.12 的另一个归约终点。
- hcomp 两条仍是我们的 IUT IV named gap，保持独立；Takkun 只能作为“3.11⇒3.12 需要单一 hull 体积上界”的参考写法。
- 若未来要统一，先补上述四个等式/对象，再谈蕴含；当前模型不匹配。


## 5. A502 语义统一：containment / hull_dominates 与我们的 hcomp

### 5.1 Takkun 两个谓词的精确语义

`PilotVolumeData.containment`:

    containment : exists g : Gamma, qPilot <= g • thetaPilot

配合 `hull_spec : forall g, g • thetaPilot <= hull` 和 `vol_mono`，只得到

    vol qPilot <= vol hull

即 q-pilot 像在 Theta-pilot 轨道/包内。它没有 height、没有 arithmeticWeight、没有 region。

`Thm311Transcription.hull_dominates` (`LogKummerCorrespondence.HullDominates`):

    def HullDominates (x0 : K.F 0) (hull : K.D) : Prop :=
      forall n : Nat, K.kummer (0 + n) (K.transport 0 n x0) <= hull

即所有 Ind3/log-Kummer 级别的像都落在 `hull` 中；配合 `volR_mono` 只得到

    volR (K.kummer n (transport ...)) <= volR hull

它的 metric 内容是 `hull` 的**接收侧体积**上界 `volR hullR <= CTheta * qVol`（hull_bound），仍没有 height。

### 5.2 我们的 hcomp 两条语义

- gap1 `height_le_normalizedRegionVolume`: `logHeight(x) <= (1+eps) * vol(region)`。这是一个 **height-to-region-volume dictionary**。
- gap2 `regionVolume_le_normalizedWeight`: `vol(region) <= (1+eps)*weight + vol(W.hull) + D`。这是 **IUT IV main estimate**：region 体积由 arithmeticWeight + theta-hull 体积 + 常数控制。

### 5.3 语义关系（逐项）

| 量/谓词 | Takkun | 我们的 hcomp | 关系 |
|---|---|---|---|
| q-pilot/weight | `qPilot`, `qVol`, `volR qPilot = -qVol` | `arithmeticWeight (abcRationalPoint a c)` | 无已证等式；需归一化/符号桥 |
| Theta hull | `hullR`, `hull_dominates`, `volR hullR` | `W.hull`, `(W.logVolume W.hull).toReal`；gap2 的加法项 | 可能是同一 hull 的两种接口；无等式 |
| 比较区域 | Takkun 无独立 region；`hullR` 是 Θ 像的 hull | `normalizedComparisonRegion W logShellPoint`（λ·(unitRegion∪point)） | hcomp gap2 的左边是 region，不是 hull；无等式 |
| q/Θ containment | `containment : qPilot <= g•thetaPilot` | 无直接对应；gap1 是 height 比较 | 不同谓词 |
| 发送侧 pin | `volS thetaPilot = arithFactor*(-qVol)`, `arithFactor=l(l+1)/12` | 无 arithFactor；用 `(1+eps)` | 无等式/因子桥 |
| 结论 | `CTheta >= -1` -> thm110 height | gap1+gap2 -> ABC height/weight contract | 不同目的地，且无桥 |

结论: `containment` 和 `hull_dominates` 都只产生 **q/Theta hull 的体积单调性**；我们的 gap1 是 height 对 region 的比较，gap2 是 region 对 weight+hull 的比较。它们不是同一命题，不能互相替代。

### 5.4 真正缺的桥对象（Lean 签名草案，均未实现）

1. **CarrierBridge**（自有 IQ 载体 ↔ Takkun PilotVolumeData/Send-Recv）:

```lean
structure CarrierBridge {X : Type u} (W : IQHullLogVolumeInterface X) where
  Omega : Type u
  ord : Preorder Omega
  vol : Omega -> Real
  vol_mono : Monotone vol
  toOmega : Set X -> Omega
  thetaHull : Omega
  qPilot : Omega
  logVolume_eq : forall S, W.logVolume S < top ->
    (W.logVolume S).toReal = vol (toOmega S)
  thetaHull_eq : toOmega W.hull = thetaHull
```

2. **RegionHullBridge**（我们的 normalizedComparisonRegion 与 Takkun hull/possible image 的同一性）:

```lean
structure RegionHullBridge {X : Type u} (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat -> Nat -> Nat -> X) where
  hullRegion : Nat -> Nat -> Nat -> Set X
  hull_eq : forall a b c, IsABCTriple a b c ->
    normalizedComparisonRegion W logShellPoint a b c = hullRegion a b c
  hullVolume_eq : forall a b c, IsABCTriple a b c ->
    (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal =
      (W.logVolume W.hull).toReal
```

3. **QPilotWeightBridge**（q-pilot 体积 ↔ arithmeticWeight，含符号/归一化）:

```lean
structure QPilotWeightBridge (W : IQHullLogVolumeInterface X) where
  qVol : Nat -> Nat -> Nat -> Real
  weight_eq : forall a b c, IsABCTriple a b c ->
    qVol a b c = arithmeticWeight (abcRationalPoint a c)
  qPilot_relation : forall a b c, IsABCTriple a b c ->
    qVol a b c = -(W.logVolume {logShellPoint a b c}).toReal
```

4. **HeightRegionBridge**（Takkun 没有 height 侧；gap1 必须独立桥）:

```lean
structure HeightRegionBridge (W : IQHullLogVolumeInterface X) where
  logShellPoint : Nat -> Nat -> Nat -> X
  height_le_region : forall a b c, IsABCTriple a b c ->
    Height.logHeight₁ (abcRationalPoint a c) <=
      (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal
```

5. **FactorBridge**（Takkun `arithFactor=l(l+1)/12` 与我们 `(1+eps)`/`D` 的常数换算）:

```lean
structure FactorBridge (l : Nat) where
  arithFactor : Real
  arithFactor_eq : arithFactor = (l * (l + 1)) / 12
  epsilon_absorbs : forall eps : Real, 0 < eps -> exists D : Real,
    forall x : Real, arithFactor * x <= (1 + eps) * x + D
```

6. **IndObjectBridge**（自有 Ind1UnitAction/Ind1Setoid/Ind2AlienLink/Ind3PossibleImage ↔ Takkun Γ/hull_dominates 的 Ind1/2/3）:

```lean
structure IndObjectBridge where
  Gamma : Type
  group : Group Gamma
  act : Gamma -> Omega -> Omega
  ind1_action_eq : ...
  ind2_copy_eq : ...
  ind3_hull_eq : ...
```

状态: 上述 6 个 bridge 对象**全部未实现**；自有真实对象只有 HodgeTheaterCore/PrimeStripCore/log-shell/hull/Haar/Ind1UnitAction，Takkun 提供 PilotVolumeData/LogKummer 形式但不提供这些桥。故 (P) 与 hcomp 仍不可比。

