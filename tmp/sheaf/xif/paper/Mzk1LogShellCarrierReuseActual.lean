/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1LogShellCarrierArithmeticActual

/-! # Reuse: corollaries of the log-shell p* arithmetic -/

namespace LeanFormal.IUT

theorem sourceLogShellStar_dvd_sq' (p : Nat) : sourceLogShellStar p ∣ p ^ 2 := by
  rw [pow_two]
  exact sourceLogShellStar_dvd_sq p

theorem sourceLogShellStar_eq_pow' (p : Nat) :
    sourceLogShellStar p = p ∨ sourceLogShellStar p = p ^ 2 := by
  rcases sourceLogShellStar_eq_pow p with h | h
  · left
    simpa using h
  · right
    simpa using h

theorem SourceLogShellDatum.pStar_eq_or_pow (D : SourceLogShellDatum) :
    D.pStar = D.p ∨ D.pStar = D.p ^ 2 := by
  rw [SourceLogShellDatum.pStar]
  exact sourceLogShellStar_eq_pow' D.p

theorem SourceLogShellDatum.pStar_dvd_p' (D : SourceLogShellDatum) : D.p ∣ D.pStar := 
  D.pStar_dvd

theorem SourceLogShellDatum.pStar_dvd_sq' (D : SourceLogShellDatum) :
    D.pStar ∣ D.p * D.p := D.pStar_dvd_sq

theorem sourceLogShellStar_mul_self_dvd (p : Nat) :
    sourceLogShellStar p * sourceLogShellStar p ∣ p * p * (p * p) := by
  have h1 : sourceLogShellStar p ∣ p * p := sourceLogShellStar_dvd_sq p
  exact mul_dvd_mul h1 h1

end LeanFormal.IUT
