/- U-R 出口 C2 装配（route §5.3 L395-406）:
  q_P5 = -M ∧ θ_P5 ≤ H_pkt := Σ_a w_a V_a，其中
  θ_P5 := ksThetaHullLogRoot T（K-side paper-weight θ 读数）;
  q_P5 := -M_paper_v2 T（paper 口径 M = Q_all/(2l)，Q_all = qPilotMagnitudePaper_v2）;
  H_pkt := ucWeightedHpkt (normDegreeWeight T) packetV。

theta 侧由 Mzk1URThetaKSideActual.ksThetaHullLogRoot_le_ucWeightedHpkt 给（输入 per-b
hperB: ksThetaHullLog b ≤ packetV b）。
q 侧把 kurt 的 hP5 终版（-M_paper_v2 ≤ ksThetaHullLogRoot，BadF 重建后到）作为显式
实际义务参数 D.hP5；不定义 fake 的 qP5_eq_neg_MpaperV2（q_P5 按 paper 口径直接定义）。
旧 qPilotRealifiedLogVolume（-MqBad）标 LEGACY，不进 C2 主链。

consumer: U-C/C3（uc_c4_actual_paper_letters 等）。 -/
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import tmp.sheaf.xif.paper.Mzk1ULKSideLettersActual
import tmp.sheaf.xif.paper.Mzk1UCC3ProducerActual
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1URC2AssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)]

/-- paper 口径 q_P5 = -M_paper_v2。 -/
noncomputable def qP5 : ℝ := - M_paper_v2 (T := T)

/-- q_P5 的定义式。 -/
theorem qP5_def : qP5 T = - M_paper_v2 (T := T) := rfl

/-- H_pkt := Σ_a w_a V_a（K-side paper-weight 加权 hull）。 -/
noncomputable def HpktUR (packetV : Bad (nativePlaceSelection T) → ℝ) : ℝ :=
  ucWeightedHpkt (normDegreeWeight T) packetV

/-- theta 侧: θ_P5 ≤ H_pkt（kurt KSide 定理 + per-b hperB）。 -/
theorem thetaP5_le_Hpkt {packetV : Bad (nativePlaceSelection T) → ℝ}
    (hperB : ∀ b, ksThetaHullLog (l := l) T b ≤ packetV b) :
    ksThetaHullLogRoot (l := l) T ≤ HpktUR T packetV :=
  ksThetaHullLogRoot_le_ucWeightedHpkt T packetV hperB

/-- C2 数据: q_P5 与 θ_P5/H_pkt 以及 kurt hP5 终版（显式实际义务）。 -/
structure URC2Data where
  packetV : Bad (nativePlaceSelection T) → ℝ
  hperB : ∀ b, ksThetaHullLog (l := l) T b ≤ packetV b
  /-- kurt 的 hP5 终版（-M_paper_v2 ≤ θ，BadF 重建后到）; 显式实际义务。 -/
  hP5 : qP5 T ≤ ksThetaHullLogRoot (l := l) T

/-- C2: q_P5 ≤ θ_P5 ≤ H_pkt。 -/
theorem c2 (D : URC2Data T) :
    qP5 T ≤ ksThetaHullLogRoot (l := l) T ∧
      ksThetaHullLogRoot (l := l) T ≤ HpktUR T D.packetV :=
  ⟨D.hP5, thetaP5_le_Hpkt T D.hperB⟩

/-- C2 合并形式: q_P5 ≤ H_pkt。 -/
theorem qP5_le_Hpkt (D : URC2Data T) : qP5 T ≤ HpktUR T D.packetV :=
  (c2 T D).1.trans (c2 T D).2

#print axioms qP5_def
#print axioms thetaP5_le_Hpkt
#print axioms c2
#print axioms qP5_le_Hpkt

end LeanFormal.IUT.XiFPaper.Mzk1URC2AssemblyActual