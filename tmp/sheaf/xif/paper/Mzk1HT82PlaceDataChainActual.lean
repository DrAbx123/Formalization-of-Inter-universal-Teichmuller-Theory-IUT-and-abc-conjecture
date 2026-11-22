/- H-T §8.2: per-place log 恒等（batch4d 真实片段）。

按 Lead 2026-11-17 de-conditionalization 指令: 条件式 RelativeDifferentNormData 不再作为
终点; 真不同项链改走 batch2/4d 实际定理 + L-侧 StepV 路线; 本文件仅保留已证真实片段。 -/
import tmp.sheaf.xif.paper.Mzk1G1RelativeDifferentLogActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HT82PlaceDataChainActual

open NumberField
open UniqueFactorizationMonoid
open LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentLogActual

universe u

variable {K : Type u} [Field K] [NumberField K] {L : Type u} [Field L] [NumberField L]
  [Algebra K L] [Module.Finite (𝓞 K) (𝓞 L)]

/-- per-place log 恒等: log|N(P)| = f_P * log|N(P.under)|（batch4d 桥真证）。 -/
theorem log_absNorm_eq_inertiaDeg_mul_log_under (P : Ideal (𝓞 L)) [hPprime : P.IsPrime]
    (hPne : P ≠ ⊥) :
    Real.log ((Ideal.absNorm P : ℕ) : ℝ) =
      (P.inertiaDeg (𝓞 K) : ℝ) *
        Real.log ((Ideal.absNorm (P.under (𝓞 K)) : ℕ) : ℝ) := by
  have hpow := absNorm_prime_eq_pow_inertiaDeg_new (K := K) (L := L) (P := P) (hP := hPne)
  have hcast : ((Ideal.absNorm P : ℕ) : ℝ) =
      ((Ideal.absNorm (P.under (𝓞 K)) : ℕ) : ℝ) ^ P.inertiaDeg (𝓞 K) := by
    rw [hpow]
    push_cast
    ring
  rw [hcast, Real.log_pow]

#print axioms log_absNorm_eq_inertiaDeg_mul_log_under

end LeanFormal.IUT.XiFPaper.Mzk1HT82PlaceDataChainActual
