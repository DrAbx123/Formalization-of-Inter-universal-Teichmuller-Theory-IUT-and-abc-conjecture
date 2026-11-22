/- C4 consumer 的 paper-normalized M 版: 用 uc_c4_of_paperConstants（M 为任意字母），
避免硬编码 γ 权 actualQPilotMagnitudeClassical 进 C4 主链。
实际字母: S_ar := SAr_tripodal T, d_mod := dMod T；Q/M/eMod/eta_prm/η0 为实际义务参数。
eta 侧另有 etaPrm 实例化版本（accepted Prop 1.6 见证）。

F-version 注（route §5.4）: S_ar 用 F 版（T.arithmetic.F）是合法的——paper L1412-1413
log dFtpd+log fFtpd <= log dF+log fF = S_F，且 L1424 给 log dK <= S_F + 2log l（无 +21 常数）;
因此 F 版 hii/hstepVIII 成立，C4 结论 c_l Q <= A_F=(1+12d_mod/l)S_F+10E_ar 比 paper 最终
F-display (1+20d_mod/l)S_F+20E_ar 更强，对 P8 足够。F_tpd 中间域对象未构造（不进入本链）。 -/
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1UCHpktActual
import tmp.sheaf.xif.paper.Mzk1ULPaperLettersActual
import tmp.sheaf.xif.paper.Mzk1UCEtaPrmActual
import tmp.sheaf.xif.paper.Mzk1ULEModActual

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1UCC4PaperActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1UCHpktActual
open LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual
open LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual
open LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b, MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b, BorelSpace (qVFamTensorBlock T b)]

/-- **C4（paper-normalized M）**: 实际 S_ar/d_mod 字母；M 为任意实际字母
（paper M = Q_paper/(2l)，不硬编码 γ 权 actualQPilotMagnitudeClassical）。
F-version: S_ar=SAr_tripodal 为 F 版（见文件头注），结论比 paper 最终 F display 强。 -/
theorem uc_c4_actual_paper {ι : Type*} [Fintype ι] (w V B : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hVB : ∀ i, V i ≤ B i)
    {η0 : ℝ} (hη0 : 0 < η0)
    (hπ : ∀ η : ℝ, η0 ≤ η →
      (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η))
    {eMod : Nat} (he : 1 ≤ eMod)
    (eta_prm Q M : ℝ) (hl : 5 ≤ (l.value : ℝ)) (heta : η0 ≤ eta_prm)
    (hP5 : -M ≤ actualThetaHullLogRoot (l := l) T)
    (htheta : actualThetaHullLogRoot (l := l) T ≤ ucWeightedHpkt w V)
    (hstepVIII :
      (∑ i : ι, w i * B i) ≤
        kappa (l.value : ℝ) * ((1 + 12 * dMod T / (l.value : ℝ)) * SAr_tripodal T
          + 2 * Real.log (l.value : ℝ) + 56
          - cL (l.value : ℝ) * Q
          + (20 / 3) * paperLstarLogs eMod (l.value : ℝ))
          - M) :
    cL (l.value : ℝ) * Q ≤ paperA (dMod T) (l.value : ℝ) (SAr_tripodal T)
      (paperEar eMod (l.value : ℝ) eta_prm) :=
  uc_c4_of_paperConstants w V B hw hVB hη0 hπ he (l.value : ℝ) eta_prm
    (SAr_tripodal T) Q M (dMod T) (actualThetaHullLogRoot (l := l) T)
    hl heta hP5 htheta hstepVIII

/-- eta 侧也实例化（eta_prm := etaPrm，accepted Prop 1.6 见证）。 -/
theorem uc_c4_actual_paper_eta {ι : Type*} [Fintype ι] (w V B : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hVB : ∀ i, V i ≤ B i)
    (Q M : ℝ) {eMod : Nat} (he : 1 ≤ eMod) (hl : 5 ≤ (l.value : ℝ))
    (hP5 : -M ≤ actualThetaHullLogRoot (l := l) T)
    (htheta : actualThetaHullLogRoot (l := l) T ≤ ucWeightedHpkt w V)
    (hstepVIII :
      (∑ i : ι, w i * B i) ≤
        kappa (l.value : ℝ) * ((1 + 12 * dMod T / (l.value : ℝ)) * SAr_tripodal T
          + 2 * Real.log (l.value : ℝ) + 56
          - cL (l.value : ℝ) * Q
          + (20 / 3) * paperLstarLogs eMod (l.value : ℝ))
          - M) :
    cL (l.value : ℝ) * Q ≤ paperA (dMod T) (l.value : ℝ) (SAr_tripodal T)
      (paperEar eMod (l.value : ℝ) LeanFormal.IUT.XiFPaper.Mzk1UCEtaPrmActual.etaPrm) :=
  uc_c4_actual_paper T w V B hw hVB LeanFormal.IUT.XiFPaper.Mzk1UCEtaPrmActual.etaPrm_pos
    (fun η h => LeanFormal.IUT.XiFPaper.Mzk1UCEtaPrmActual.primeCounting_le_four_thirds h)
    he LeanFormal.IUT.XiFPaper.Mzk1UCEtaPrmActual.etaPrm Q M hl le_rfl hP5 htheta hstepVIII

#print axioms uc_c4_actual_paper
#print axioms uc_c4_actual_paper_eta
/-- **paper 字母全实例化（除 Q/M 与三个实际义务）**: eMod := eMod T, eta_prm := etaPrm,
S_ar := SAr_tripodal T, d_mod := dMod T。 -/
theorem uc_c4_actual_paper_letters {ι : Type*} [Fintype ι] (w V B : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hVB : ∀ i, V i ≤ B i)
    (Q M : ℝ) (hl : 5 ≤ (l.value : ℝ))
    (hP5 : -M ≤ actualThetaHullLogRoot (l := l) T)
    (htheta : actualThetaHullLogRoot (l := l) T ≤ ucWeightedHpkt w V)
    (hstepVIII :
      (∑ i : ι, w i * B i) ≤
        kappa (l.value : ℝ) * ((1 + 12 * dMod T / (l.value : ℝ)) * SAr_tripodal T
          + 2 * Real.log (l.value : ℝ) + 56
          - cL (l.value : ℝ) * Q
          + (20 / 3) * paperLstarLogs (LeanFormal.IUT.XiFPaper.Mzk1ULEModActual.eMod T) (l.value : ℝ))
          - M) :
    cL (l.value : ℝ) * Q ≤ paperA (dMod T) (l.value : ℝ) (SAr_tripodal T)
      (paperEar (LeanFormal.IUT.XiFPaper.Mzk1ULEModActual.eMod T) (l.value : ℝ)
        LeanFormal.IUT.XiFPaper.Mzk1UCEtaPrmActual.etaPrm) :=
  uc_c4_actual_paper_eta T w V B hw hVB Q M
    (LeanFormal.IUT.XiFPaper.Mzk1ULEModActual.one_le_eMod T) hl hP5 htheta hstepVIII

#print axioms uc_c4_actual_paper_letters

end LeanFormal.IUT.XiFPaper.Mzk1UCC4PaperActual