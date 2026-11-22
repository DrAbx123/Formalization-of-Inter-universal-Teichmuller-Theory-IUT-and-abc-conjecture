import tmp.sheaf.xif.paper.S1567AbsNormNatGeneratorActual
import tmp.sheaf.xif.paper.S1087Q1UContainmentActual
import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.S1072CanonicalQ1URegionActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1665OriginalReadoutInequalityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.S1087Q1UContainmentActual
open LeanFormal.IUT.XiFPaper.S1567AbsNormNatGeneratorActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S1072CanonicalQ1URegionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual

universe u ua uv upi umon ui

/-! ## A. 原文 Cor. 3.12 的全局 readout 不等式（目标；未证明） -/

/-- 原文 IUT III Cor. 3.12 的 signed log-volume 比较:
    -|log Theta| >= -|log q|,
    在项目中写作 qPilotSignedLogVolume <= thetaHullSignedLogVolume。
    定义域是同一源输入 I 的全局 multiradial output/hull 数据（R,n），
    方向为 <=；它不是 tensor block 上的 lattice inclusion。 -/
def S1665OriginalCor312
    {l : PrimeGeFive} {V : Type uv} [Fintype V]
    {I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V}
    (R : forall v : V, I.SourceImageRealization v)
    (n : Theorem311Source.OriginalInput.ThetaPilotCarrier l) : Prop :=
  I.qPilotSignedLogVolume <= thetaHullSignedLogVolume (I := I) R n

/-- 全局 Cor. 3.12 的现成消费者陈述（只命名，不证明）。 -/
abbrev S1665Cor312Consumer
    {l : PrimeGeFive} {V : Type uv} [Fintype V]
    {I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V}
    (R : forall v : V, I.SourceImageRealization v)
    (n : Theorem311Source.OriginalInput.ThetaPilotCarrier l) : Prop :=
  qPilotThetaHullComparison (I := I) R n

/-! ## B. 局部系数影子：S1087CoeffLe（S1567 actual） -/

/-- 固定源数据 T,b 上的原文 q/Theta 局部系数影子:
    cRoot <= cQ。这是 S1087CoeffLe，不是 F(0)/O_hol lattice 陈述。 -/
def S1665LocalCoeffShadow
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [forall b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [forall b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (b : Bad (nativePlaceSelection T)) : Prop :=
  forall i : qVFamTensorV,
    paperRootCoefficientFamily (l := l) T b i <= qVFamPureCoefficient T b i

/-- S1567 actual 结果: 局部系数影子成立。 -/
theorem s1665LocalCoeffShadow_actual
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [forall b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [forall b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (b : Bad (nativePlaceSelection T)) :
    S1665LocalCoeffShadow (l := l) T b := by
  simpa [S1665LocalCoeffShadow, S1087CoeffLe] using
    s1567CoeffLe_actual (l := l) T b

/-- 局部系数影子推出局部区域比较（actual）：qPilotQ1URegion ⊆ paperLambdaORegion cRoot。 -/
theorem s1665LocalRegion_actual
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [forall b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [forall b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (b : Bad (nativePlaceSelection T)) :
    qPilotQ1URegion (l := l) T b <=
      paperLambdaORegion (l := l) T b (paperRootCoefficientFamily (l := l) T b) :=
  s1087RegionContainment (l := l) T b
    (by
      simpa [S1087CoeffLe, S1665LocalCoeffShadow] using
        s1665LocalCoeffShadow_actual (l := l) T b)

end LeanFormal.IUT.XiFPaper.S1665OriginalReadoutInequalityActual

end
