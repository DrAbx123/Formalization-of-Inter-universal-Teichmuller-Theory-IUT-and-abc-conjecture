/- local log 量的 rational-prime 层定义（paper Def1.9(ii) deg_E；域 = Ftpd = Q(lam)，Lead 裁 (A)）:
   fiber: V(Ftpd)_p = primesOverFinset (span {p}) (O Ftpd);
   localFSum p = Sum_{v|p} f_v (deg_E 分母);
   localLogS p = (Sum_{v|p} e_v f_v log p)/localFSum;
   localLogD p = (Sum_{v|p} delta_v f_v log p)/localFSum
     (delta_v = normalizedFactors (differentIdeal Z (O Ftpd)) count v, Ftpd/Q 绝对 different);
   localLogF p bad = (Sum_{v|p, v in bad} f_v log p)/localFSum。
   目标恒等: Sum_p localLogD p * localFSum p = log |N(diff Ftpd/Q)| = [Ftpd:Q]*logDifferentF Ftpd。
   raw 版本通过乘回 localFSum 对接。 -/
import tmp.sheaf.xif.paper.Mzk1ULSArFtpdIdentityActual
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadLocalLogActual

open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalFieldActual
open LeanFormal.IUT.XiFPaper.ULTripodalNumberField
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open NumberField

variable (lam : ℂ) [NumberField ↥(FtpdLam lam)]

variable (p : Nat) [hp : Fact p.Prime]

noncomputable def fiberFtpd : Finset (Ideal (𝓞 (↥(FtpdLam lam)))) :=
  IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 (↥(FtpdLam lam)))

noncomputable def localFSum : ℝ :=
  ∑ v ∈ fiberFtpd (lam := lam) p, ((v.inertiaDeg ℤ : ℝ))

noncomputable def localLogS : ℝ :=
  (∑ v ∈ fiberFtpd (lam := lam) p,
      (Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) v : ℝ) *
        ((v.inertiaDeg ℤ : ℝ)) * Real.log (p : ℝ)) / localFSum (lam := lam) p

noncomputable def localLogD : ℝ :=
  (∑ v ∈ fiberFtpd (lam := lam) p,
      ((normalizedFactors (differentIdeal ℤ (𝓞 (↥(FtpdLam lam))))).count v : ℝ) *
        ((v.inertiaDeg ℤ : ℝ)) * Real.log (p : ℝ)) / localFSum (lam := lam) p

noncomputable def localLogF (bad : Set (Ideal (𝓞 (↥(FtpdLam lam))))) : ℝ :=
  (∑ v ∈ (fiberFtpd (lam := lam) p).filter (fun v => v ∈ bad),
      ((v.inertiaDeg ℤ : ℝ)) * Real.log (p : ℝ)) / localFSum (lam := lam) p

end


/-! ## s^Fmod 的局部量（paper L1461-1501: s^Fmod_ADiv = Sum e_v v on V(Fmod)^dst）
    注意域是 Fmod，不是 Ftpd；per-place 不等式把它与 Ftpd 的 localLogD/F 比较。 -/

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

section FmodSection

variable (q : Nat) [hq : Fact q.Prime]

/-- q 上的 Fmod 素位集合。 -/
noncomputable def fiberFmod : Finset (Ideal (𝓞 (T.arithmetic.Fmod))) :=
  IsDedekindDomain.primesOverFinset (Ideal.span {(q : ℤ)}) (𝓞 (T.arithmetic.Fmod))

/-- s^Fmod 的 deg_E 分母: Sum_{v|q} f_v（Fmod 纤维）。 -/
noncomputable def localFSumFmod : ℝ :=
  ∑ v ∈ fiberFmod (T := T) q, ((v.inertiaDeg ℤ : ℝ))

/-- **localLogS（Fmod 纤维，e_v = Fmod/Q 分歧指数）**: (Sum e_v f_v log q)/(Sum f_v)。 -/
noncomputable def localLogS_Fmod : ℝ :=
  (∑ v ∈ fiberFmod (T := T) q,
      (Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v : ℝ) *
        ((v.inertiaDeg ℤ : ℝ)) * Real.log (q : ℝ)) / localFSumFmod (T := T) q

/-- term-wise: log q <= localLogS_Fmod（每 e_v >= 1, f_v >= 0, log q >= 0）。 -/
/-- raw 版本（paper Def1.9 的分子，不除 deg_E 分母）: Sum_{v|q} e_v f_v log q。 -/
noncomputable def localLogSRaw : ℝ :=
  ∑ v ∈ fiberFmod (T := T) q,
    (Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v : ℝ) *
      ((v.inertiaDeg ℤ : ℝ)) * Real.log (q : ℝ)

/-- localLogS_Fmod = localLogSRaw / localFSumFmod（deg_E 归一，纯定义）。 -/
theorem localLogS_Fmod_eq_raw_div :
    localLogS_Fmod (T := T) q = localLogSRaw (T := T) q / localFSumFmod (T := T) q := rfl

/-- 乘回: localFSumFmod * localLogS_Fmod = localLogSRaw（除法恒等，需 localFSumFmod != 0）。 -/
theorem localFSum_mul_localLogS_Fmod (hden : localFSumFmod (T := T) q ≠ 0) :
    localFSumFmod (T := T) q * localLogS_Fmod (T := T) q = localLogSRaw (T := T) q := by
  rw [localLogS_Fmod_eq_raw_div]
  field_simp
theorem log_le_localLogS_Fmod (hlogq : 0 ≤ Real.log (q : ℝ)) :
    Real.log (q : ℝ) ≤ localLogS_Fmod (T := T) q := by
  unfold localLogS_Fmod
  have hnum : (∑ v ∈ fiberFmod (T := T) q,
      (Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v : ℝ) *
        ((v.inertiaDeg ℤ : ℝ))) ≥ (∑ v ∈ fiberFmod (T := T) q, ((v.inertiaDeg ℤ : ℝ))) := by
    apply Finset.sum_le_sum
    intro v _
    have he : (1 : ℝ) ≤ (Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v : ℝ) := by
      exact_mod_cast (Ideal.ramificationIdx'_pos (p := Ideal.span {(q : ℤ)}) (P := v))
    have hf : (0 : ℝ) ≤ (v.inertiaDeg ℤ : ℝ) := by positivity
    nlinarith
  have hden : 0 ≤ localFSumFmod (T := T) q := by
    unfold localFSumFmod
    apply Finset.sum_nonneg
    intro v _
    positivity
  rw [ge_iff_le] at hnum
  have hmul : Real.log (q : ℝ) * localFSumFmod (T := T) q ≤
      (∑ v ∈ fiberFmod (T := T) q,
        (Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v : ℝ) *
          ((v.inertiaDeg ℤ : ℝ))) * Real.log (q : ℝ) := by
    have := mul_le_mul_of_nonneg_right hnum hlogq
    rw [Finset.sum_mul] at this
    nlinarith
  have hnum2 : (∑ v ∈ fiberFmod (T := T) q,
      (Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v : ℝ) *
        ((v.inertiaDeg ℤ : ℝ)) * Real.log (q : ℝ)) =
      (∑ v ∈ fiberFmod (T := T) q,
        (Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v : ℝ) *
          ((v.inertiaDeg ℤ : ℝ))) * Real.log (q : ℝ) := by
    rw [Finset.sum_mul]
  rw [hnum2]
  apply (le_div_iff₀ hden).mpr
  nlinarith

end FmodSection


/-! ## 求和恒等式（两个归一候选，须与 paper L1572 对齐后二选一）
  (A) raw 归一: log(s^Fmod) = Sum_p localLogSRaw_p；
  (B) deg_E 归一: log(s^Fmod) = (1/[Fmod:Q]) Sum_p localFSum_p * localLogS_p。
  (A)=(B) 由 localFSum_mul_localLogS_Fmod 等价；本件只记定义，global 链待 Lead 确认。 -/

section SumIdentityFacts

variable (q : Nat) [hq : Fact q.Prime]

/-- (B) 的逐项改写: localFSum*localLogS = raw（与上面同一条，重复导出便于引用）。 -/
theorem sum_identity_term (hden : localFSumFmod (T := T) q ≠ 0) :
    localFSumFmod (T := T) q * localLogS_Fmod (T := T) q = localLogSRaw (T := T) q :=
  localFSum_mul_localLogS_Fmod (T := T) q hden

end SumIdentityFacts

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadLocalLogActual