/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier

/-! # Reuse: computation corollaries for the log-shell carrier (tree asset) -/

namespace LeanFormal.IUT

theorem SourceLogShellDatum.pStar_eq_star (D : SourceLogShellDatum) :
    D.pStar = sourceLogShellStar D.p := rfl

theorem SourceLogShellDatum.pStar_pos' (D : SourceLogShellDatum) (hp : 0 < D.p) :
    0 < D.pStar := by
  rw [SourceLogShellDatum.pStar_eq_star]
  exact sourceLogShellStar_pos hp

theorem SourceLogShellDatum.pStar_dvd_p_star (D : SourceLogShellDatum) :
    D.p ∣ D.pStar := by
  rw [SourceLogShellDatum.pStar_eq_star]
  exact sourceLogShellStar_dvd D.p

theorem SourceLogShellDatum.pStar_mul_dvd_sq (D : SourceLogShellDatum) :
    D.pStar * D.pStar ∣ D.p * D.p * (D.p * D.p) := by
  have h : D.pStar ∣ D.p * D.p := by
    rw [SourceLogShellDatum.pStar_eq_star]
    exact sourceLogShellStar_dvd_sq D.p
  exact mul_dvd_mul h h

end LeanFormal.IUT
