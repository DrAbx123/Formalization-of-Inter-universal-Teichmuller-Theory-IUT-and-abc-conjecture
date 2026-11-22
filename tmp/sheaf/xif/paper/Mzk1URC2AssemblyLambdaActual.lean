/- U-R C2 assembly（λ 权版, route §5.3 L395-406）:
  theta_P5 := paperThetaHullLogRoot_lam（kurt adapter: ksThetaHullLogRoot_lam）;
  q_P5 := -M_paper_v2（paper Q=h=Q_all 口径, v2）;
  H_pkt := paperHpkt T packetV = ucWeightedHpkt (thetaLamWeight T) packetV;
  theta≤Hpkt 由 kurt adapter paperThetaHullLogRoot_le_Hpkt 给;
  q≤theta（hP5）是 kurt 终端归约/ J1 同 q 桥的实际义务，作为 URC2LamData 字段显式给出，不 fake。
  依赖 adapter Mzk1URThetaKLambdaAdapterActual（START 23:38:12）。 -/
import tmp.sheaf.xif.paper.Mzk1URThetaKLambdaAdapterActual
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1URC2AssemblyLambdaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLambdaAdapterActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-- paper 口径 q_P5 = -M_paper_v2。 -/
noncomputable def qP5Lam : ℝ := - M_paper_v2 (T := T)

/-- q_P5 定义式。 -/
theorem qP5Lam_def : qP5Lam T = - M_paper_v2 (T := T) := rfl

/-- theta_P5（λ 权 paper 读数）。 -/
noncomputable abbrev thetaP5Lam : ℝ := paperThetaHullLogRoot_lam (l := l) T

/-- H_pkt（λ 权）。 -/
noncomputable abbrev HpktUR_lam (packetV : Bad (nativePlaceSelection T) → ℝ) : ℝ :=
  paperHpkt (l := l) T packetV

/-- theta ≤ H_pkt（kurt adapter）。 -/
theorem thetaP5Lam_le_Hpkt_lam {packetV : Bad (nativePlaceSelection T) → ℝ}
    (hperB : ∀ b, ksThetaHullLog (l := l) T b ≤ packetV b) :
    thetaP5Lam (l := l) T ≤ HpktUR_lam (l := l) T packetV :=
  paperThetaHullLogRoot_le_Hpkt (l := l) T packetV hperB

/-- C2 λ 权数据: theta≤Hpkt 已证；hP5 是 kurt 终端归约/J1 桥的实际义务（显式）。 -/
structure URC2LamData where
  packetV : Bad (nativePlaceSelection T) → ℝ
  hperB : ∀ b, ksThetaHullLog (l := l) T b ≤ packetV b
  /-- kurt hP5 终版（q_P5 ≤ theta_P5）；由 neg_MpaperV2_le_thetaLam_of_bridge/J1 提供。 -/
  hP5 : qP5Lam (l := l) T ≤ thetaP5Lam (l := l) T

/-- C2: q_P5 ≤ theta_P5 ≤ H_pkt。 -/
theorem c2Lam (D : URC2LamData T) :
    qP5Lam (l := l) T ≤ thetaP5Lam (l := l) T ∧
      thetaP5Lam (l := l) T ≤ HpktUR_lam (l := l) T D.packetV :=
  ⟨D.hP5, thetaP5Lam_le_Hpkt_lam (l := l) T D.hperB⟩

/-- 合并: q_P5 ≤ H_pkt。 -/
theorem qP5Lam_le_Hpkt (D : URC2LamData T) :
    qP5Lam (l := l) T ≤ HpktUR_lam (l := l) T D.packetV :=
  (c2Lam (l := l) T D).1.trans (c2Lam (l := l) T D).2

#print axioms qP5Lam_def
#print axioms thetaP5Lam_le_Hpkt_lam
#print axioms c2Lam
#print axioms qP5Lam_le_Hpkt

end LeanFormal.IUT.XiFPaper.Mzk1URC2AssemblyLambdaActual
