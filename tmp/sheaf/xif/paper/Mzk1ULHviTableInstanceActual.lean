/- U-C Step (viii) (beta) 条件式实例化（Lead 2026-11-17 裁决 (B)）。

本文件把 david 的 Mzk1ULHviTableFinalActual.hviTable_final 实例化到实际 T 数据:
  * b := Bad (nativePlaceSelection T), γ := nativeBadLocalWeight T;
  * V b j := 实际 possible-images holomorphic hull 的归一化 log-volume,
    经 kurt 的 Mzk1URCollectionLayerActual.urCollHullLog（region family 由 hullSet
    给出，generic helper 不展开具体 tensor block 以避免 isDefEq 超时）;
  * 字母 D/Q/logP/Tl 由调用方给出（最终取自 urCollLocalNormOrder/urCollOq/
    urCollLogp/urCollIotaL）。

hVh 为具名 RETAINED 参数，provenance:
  route §5.4 Step (v)-(vi) 的 possible-images holomorphic hull 几何识别;
  上游界用 accepted donor LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
  .arithmeticTuple_stepV_hull_normalizedLogVolume_le_paperBound (L814) 及
  .arithmeticTupleNormalizedLogVolume_le_stepVPaperBound (L524)。
  几何识别本身是 route 新证明（Lead 裁决 (A) 阶段, 等 kurt per-label defs）。
本文件不冒充 hVh 已证, 仅把 C4 条件清单缩为 htheta+hiii+hvii+hX+hVh。 -/
import tmp.sheaf.xif.paper.Mzk1ULHviTableFinalActual
import tmp.sheaf.xif.paper.Mzk1URLabelDataActual
import tmp.sheaf.xif.paper.Mzk1StepVExtraNonnegActual
import tmp.sheaf.xif.paper.Mzk1URCollectionLayerActual
import tmp.sheaf.xif.paper.Mzk1ULPacketFamilyActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHviTableInstanceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1URCollectionLayerActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHviTableFinalActual
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open MeasureTheory

universe u v w

/-! ## Generic hull-log helper（轻量, 不展开具体 tensor block） -/

/-- 泛型 per-label hull log-volume: 实际 normalized log-volume 的 region family 实例。
不展开具体 tensor block 类型（避免 isDefEq 超时）。 -/
noncomputable def urCollHullLogFamily
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
    (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (hullSet : Nat → Set (ArithmeticTensorTupleBlock places tuple)) (j : Nat) : Real :=
  urCollHullLog places tuple (hullSet j)

/-! ## 条件式 T-side 实例 -/

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- s3014 := Σ_b γ_b·(1/n)Σ_label V_b,label（bad-place 加权聚合的 per-label hull 平均）。 -/
noncomputable def hviTableS3014
    (V : Bad (nativePlaceSelection T) → Nat → Real) (n : Nat) : Real :=
  ∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b *
    ((1 / (n : Real)) * (∑ label ∈ Finset.Icc 1 n, V b label))

/-- **条件式 hviTable 实例（(B) 裁决）**：V 为 per-label hull log-volume
（可实例化为 urCollHullLogFamily）；hVh 为具名 retained 参数
（provenance: route §5.4 possible-images hull + accepted L814/L524）。
由 hviTable_final 得 bad 加权聚合上界，字母为 bad 加权平均的 D/Q/logP/Tl。 -/
theorem hviTable_instance
    (n : Nat) (hn : 2 ≤ n)
    (logP D Q Tl : Bad (nativePlaceSelection T) → Real)
    (V : Bad (nativePlaceSelection T) → Nat → Real)
    (hVh : ∀ b : Bad (nativePlaceSelection T), ∀ label ∈ Finset.Icc 1 n,
      V b label ≤
        collectionBound (2 * (n : Real) + 1) (D b) (Q b) (logP b) (Tl b) label) :
    hviTableS3014 T V n ≤
      (1 / (n : Real)) * (∑ j ∈ Finset.Icc 1 n,
        collectionBound (2 * (n : Real) + 1)
          (∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b * D b)
          (∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b * Q b)
          (∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b * logP b)
          (∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b * Tl b) j) := by
  have hγ0 : ∀ b : Bad (nativePlaceSelection T), 0 ≤ nativeBadLocalWeight T b := by
    intro b
    rw [nativeBadLocalWeight_eq_inv (T := T)]
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  have h := hviTable_final (b := Bad (nativePlaceSelection T)) (γ := nativeBadLocalWeight T)
    hγ0 n hn logP D Q Tl V hVh
  simpa [hviTableS3014] using h


/-- (A) 比较引理（纯实数字母算术, 消费 accepted Step(v) paper 界 + exceptional 界）:
若 actual <= (-lam + d + 1)*logp + exc（L524/L814 的输出形状）、exc <= 4(j+1)*Tl、
D = d*logp、Q = oq*logp、lam*logp = (j^2/(2l))*Q（l = 2n+1），
则 actual <= collectionBound (2n+1) D Q logp Tl j（donor 的 S 槽 = logp）。 -/
theorem hullLog_le_collectionBound_of_paperBound
    (n j : Nat) (logp D Q Tl lam d oq exc actual : Real)
    (hlogp : 0 ≤ logp) (hd : 0 ≤ d)
    (hD : D = d * logp) (hQ : Q = oq * logp)
    (hlambda : lam * logp = ((j : Real) ^ 2 / (2 * (2 * (n : Real) + 1))) * Q)
    (hpaper : actual ≤ (-lam + d + 1) * logp + exc)
    (hexc : exc ≤ 4 * ((j : Real) + 1) * Tl) :
    actual ≤ collectionBound (2 * (n : Real) + 1) D Q logp Tl j := by
  unfold collectionBound
  rw [hD, hQ]
  have hcq : ((j : Real) ^ 2 / (2 * (2 * (n : Real) + 1))) * (oq * logp) = lam * logp := by
    rw [← hQ]
    exact hlambda.symm
  rw [hcq]
  have hjd : 0 ≤ (j : Real) * (d * logp) :=
    mul_nonneg (Nat.cast_nonneg j) (mul_nonneg hd hlogp)
  linarith [hpaper, hexc, hjd]


/-- (A) 专门化到 sophie 的 label 字母定义（Mzk1URLabelDataActual）:
由 L524/L814 的 paper 界（actual <= (-labelLambda + labelDifferentSum + 1)*logp + exc）
与 exceptional 界（exc <= 4(j+1)*labelTl），直接得 donor collectionBound 上界，
字母: D = labelD d logp, Q = labelQ oq logp, S = labelLogP p, T = labelTl eMod l。 -/
theorem hVh_of_paperBound_letters
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] {V : ι → Type w}
    (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
    (n j : Nat) (hn : 2 ≤ n) (oq : Real) (eMod : Nat) (exc actual : Real)
    (hdiff : 0 ≤ LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelDifferentSum places tuple)
    (hpaper : actual ≤
      (-LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLambda (2 * (n : Real) + 1) oq j +
          LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelDifferentSum places tuple + 1) *
        LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLogP p + exc)
    (hexc : exc ≤ 4 * ((j : Real) + 1) *
      LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelTl eMod (2 * (n : Real) + 1)) :
    actual ≤ collectionBound (2 * (n : Real) + 1)
      (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelD
        (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelDifferentSum places tuple)
        (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLogP p))
      (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelQ oq
        (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLogP p))
      (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLogP p)
      (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelTl eMod (2 * (n : Real) + 1)) j := by
  have hlogp : 0 ≤ LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLogP p := by
    unfold LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLogP
    exact Real.log_nonneg (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  refine hullLog_le_collectionBound_of_paperBound n j
    (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLogP p)
    (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelD
      (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelDifferentSum places tuple)
      (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLogP p))
    (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelQ oq
      (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLogP p))
    (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelTl eMod (2 * (n : Real) + 1))
    (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLambda (2 * (n : Real) + 1) oq j)
    (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelDifferentSum places tuple)
    oq exc actual hlogp hdiff rfl rfl ?_ hpaper hexc
  · unfold LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLambda
    unfold LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelQ
    ring


/-- (A) 不同除子阶非负: labelDifferentSum places tuple >= 0（复用旧件已 DONE 的
Mzk1StepVExtraNonnegActual.localNormOrder_arithmeticTupleLocalDifferent_nonneg, API 层）。 -/
theorem labelDifferentSum_nonneg
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] {V : ι → Type w}
    (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i) :
    0 ≤ LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelDifferentSum places tuple := by
  unfold LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelDifferentSum
  exact Finset.sum_nonneg fun i _ =>
    LeanFormal.IUT.XiFPaper.Mzk1StepVExtraNonnegActual.localNormOrder_arithmeticTupleLocalDifferent_nonneg
      (p := p) places tuple i

/-- (A) hVh 字母桥（去掉 hdiff 参数版）: 直接复用已证的 labelDifferentSum_nonneg。 -/
theorem hVh_of_paperBound_letters'
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] {V : ι → Type w}
    (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
    (n j : Nat) (hn : 2 ≤ n) (oq : Real) (eMod : Nat) (exc actual : Real)
    (hpaper : actual ≤
      (-LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLambda (2 * (n : Real) + 1) oq j +
          LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelDifferentSum places tuple + 1) *
        LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLogP p + exc)
    (hexc : exc ≤ 4 * ((j : Real) + 1) *
      LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelTl eMod (2 * (n : Real) + 1)) :
    actual ≤ collectionBound (2 * (n : Real) + 1)
      (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelD
        (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelDifferentSum places tuple)
        (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLogP p))
      (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelQ oq
        (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLogP p))
      (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLogP p)
      (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelTl eMod (2 * (n : Real) + 1)) j :=
  hVh_of_paperBound_letters places tuple n j hn oq eMod exc actual
    (labelDifferentSum_nonneg places tuple) hpaper hexc


/-- (A) 已证 hVh（条件式，消费 sophie 的 LabelStepVHullData）:
由 D.hpaper（L814 输出）+ D.hexc（R4 型 exceptional 界）+ labelDifferentSum_nonneg
+ hVh_of_paperBound_letters' 得 donor collectionBound 上界。 -/
theorem hVh_of_labelData
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
    (istar : ι) (exceptional : Finset ι) (n : Nat) (hn : 2 ≤ n) (oq : Real) (eMod : Nat)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (D : LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.LabelStepVHullData
      places tuple istar exceptional n oq eMod) :
    ∀ j ∈ Finset.Icc 1 n,
      urCollHullLogFamily places tuple D.hullSet j ≤
        collectionBound (2 * (n : Real) + 1)
          (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelD
            (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelDifferentSum places tuple)
            (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLogP p))
          (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelQ oq
            (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLogP p))
          (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLogP p)
          (LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelTl eMod (2 * (n : Real) + 1)) j := by
  intro j hj
  have hpaper : urCollHullLogFamily places tuple D.hullSet j ≤
      (-LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLambda (2 * (n : Real) + 1) oq j +
          LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelDifferentSum places tuple + 1) *
        LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelLogP p +
        ∑ i ∈ exceptional, (3 + Real.log
          (logShellRamificationExponent
            (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real)) := by
    simpa [urCollHullLogFamily,
      LeanFormal.IUT.XiFPaper.Mzk1URCollectionLayerActual.urCollHullLog] using D.hpaper j
  exact hVh_of_paperBound_letters' places tuple n j hn oq eMod _ _ hpaper (D.hexc j)


#print axioms hVh_of_labelData

end LeanFormal.IUT.XiFPaper.Mzk1ULHviTableInstanceActual
