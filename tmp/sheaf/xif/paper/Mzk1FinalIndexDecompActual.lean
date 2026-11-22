/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1IndexQFEConnectionActual
import tmp.sheaf.xif.paper.Mzk1TorsionSplitActual
import tmp.sheaf.xif.paper.Mzk1CeilDecompActual
import tmp.sheaf.xif.paper.Mzk1QuotientDecompActual
import tmp.sheaf.xif.paper.Mzk1IndexPowIdentityActual
import Mathlib.Tactic
/-! # Final decomposition of the log-shell index with correction factor -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1FinalIndexDecompActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Mzk1TorsionSplitActual
open LeanFormal.IUT.XiFPaper.Mzk1CeilDecompActual
open LeanFormal.IUT.XiFPaper.Mzk1QuotientDecompActual
open LeanFormal.IUT.XiFPaper.Mzk1IndexPowIdentityActual
open LeanFormal.IUT.XiFPaper.Mzk1IndexQFEConnectionActual
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
variable [FiniteDimensional (Padic p) K]
include localNormedAlgebra
/-- Final index decomposition with explicit correction factor. -/
theorem index_decomp_with_correction
    {f : Nat} (hf : 0 < f)
    (hq : logShellResidueCard (K := K) = p ^ f)
    (hdecomp : Nat.card (CommGroup.torsion (Integers K)ˣ) *
      logShellIntegerIndex (K := K) (p := p) =
      logShellResidueCard (K := K) ^
          (logShellRamificationExponent (K := K) (p := p) *
            logShellScaleExponentFactor (p := p) - 1) *
        (logShellResidueCard (K := K) - 1)) :
    ∃ (a c : Nat),
      logShellIntegerIndex (K := K) (p := p) =
        logShellResidueCard (K := K) ^ a * c ∧
      LogShellResiduePowerCardCorrectionHypothesis (K := K) (p := p) a c := by
  classical
  let A := logShellRamificationExponent (K := K) (p := p) *
    logShellScaleExponentFactor (p := p) - 1
  let T := Nat.card (CommGroup.torsion (Integers K)ˣ)
  let q := logShellResidueCard (K := K)
  have hqA : q = p ^ f := hq
  have hTpos : 0 < T := by
    dsimp [T]
    letI := finite_integralUnitTorsion (K := K) (p := p)
    exact Nat.card_pos
  have hdvd : T ∣ q ^ A * (q - 1) := ⟨logShellIntegerIndex (K := K) (p := p), hdecomp.symm⟩
  have hp : p.Prime := Fact.out
  have hcop : Nat.Coprime p (q - 1) := by
    dsimp [q]
    exact coprime_p_logShellResidueCard_sub_one (K := K) (p := p)
  obtain ⟨m, T0, hT, hcopT0, hT0dvd, hmle⟩ :=
    torsion_split hp hTpos hdvd hcop hqA
  have hT0pos : 0 < T0 := by
    by_contra h0
    have hzero : T0 = 0 := Nat.eq_zero_of_not_pos h0
    rw [hzero, mul_zero] at hT
    omega
  obtain ⟨k, r, hkr, hr, hkA⟩ := ceil_decomp hf hmle
  have hExp : f * A - m = f * (A - k) + r :=
    exponent_decomp hkA hkr hmle
  have hdiv := quotient_decomp (p := p) (q := q) (f := f) (A := A) (m := m)
    (T0 := T0) (T := T) (Fact.out : p.Prime).pos hT0pos hqA hT hT0dvd hmle
  have hpow := index_pow_identity (p := p) (q := q) (f := f) (A := A)
    (m := m) (k := k) (r := r) (T0 := T0) hqA hExp
  have hbase : logShellIntegerIndex (K := K) (p := p) = q ^ A * (q - 1) / T := by
    simpa [T, q, A] using (Nat.eq_div_of_mul_eq_right (ne_of_gt hTpos) hdecomp)
  have hidx : logShellIntegerIndex (K := K) (p := p) = q ^ (A - k) *
      (p ^ r * ((q - 1) / T0)) := by
    rw [hbase, hdiv, hpow]
  refine ⟨A - k, p ^ r * ((q - 1) / T0), hidx, ?_⟩
  unfold LogShellResiduePowerCardCorrectionHypothesis
  change Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) =
    q ^ (A - k) * Nat.card (CommGroup.torsion (Integers K)ˣ) *
      (p ^ r * ((q - 1) / T0))
  rw [qfe_quotient_card_actual (K := K) (p := p)]
  calc q ^ A * (q - 1)
      = T * logShellIntegerIndex (K := K) (p := p) := hdecomp.symm
    _ = T * (q ^ (A - k) * (p ^ r * ((q - 1) / T0))) := by rw [hidx]
    _ = q ^ (A - k) * T * (p ^ r * ((q - 1) / T0)) := by ring
    _ = q ^ (A - k) * Nat.card (CommGroup.torsion (Integers K)ˣ) *
          (p ^ r * ((q - 1) / T0)) := by rfl
end LeanFormal.IUT.XiFPaper.Mzk1FinalIndexDecompActual
end