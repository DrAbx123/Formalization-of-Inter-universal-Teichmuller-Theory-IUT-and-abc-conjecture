/- Route 4.5 CTheta lower-bound bridge (R0/R2 assembly).
   Hypotheses (all explicit; no fake equality CThetaPaper = thetaLogVolume/M):
     (R0) M = paperQAbsLog reading: M > 0 case,
     (R1) -M <= ksThetaHullLogRoot_lam reading: -M <= theta,
     (R2 packet upper) theta <= kappa_l (A - c_l Q) - M,
     (CTheta reading) CTheta = theta / M  -- explicit route/paper reading, supplied by caller.
   Conclusion: -1 <= CTheta (paper IV L1365-1376; route 4.5), and M=0 degeneracy handled separately.
   Do NOT assert CThetaPaper = thetaLogVolume/M as a theorem; only this implication. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULCThetaFromR0R1Actual

/-- CTheta lower bound from R1/R2 + CTheta reading (M>0, divide by M). -/
theorem cTheta_ge_neg_one_of_bounds
    (M theta Q A cL kappa CTheta : Real)
    (hM : 0 < M)
    (hR1 : -M ≤ theta)
    (hpack : theta ≤ kappa * (A - cL * Q) - M)
    (hCTheta : CTheta = theta / M) :
    -1 ≤ CTheta := by
  rw [hCTheta]
  rw [le_div_iff₀ hM]
  linarith

/-- M=0 degeneracy: Q = 2lM = 0 (Mpaper relation) and packet bound remains; no CTheta lower bound forced. -/
theorem m_eq_zero_degeneracy
    (M l Q : Real) (hM : M = 0)
    (hQ : Q = 2 * l * M) :
    Q = 0 := by
  rw [hM] at hQ
  linarith

/-- M>0 monotone form: -M <= theta <= theta_packet - M and CTheta=theta/M => -1 <= CTheta <= ... -/
theorem cTheta_sandwich
    (M theta thetaU CTheta : Real) (hM : 0 < M)
    (hR1 : -M ≤ theta) (hup : theta ≤ thetaU)
    (hCTheta : CTheta = theta / M) :
    -1 ≤ CTheta := by
  rw [hCTheta]
  rw [le_div_iff₀ hM]
  linarith

#print axioms cTheta_ge_neg_one_of_bounds
#print axioms m_eq_zero_degeneracy
#print axioms cTheta_sandwich

end LeanFormal.IUT.XiFPaper.Mzk1ULCThetaFromR0R1Actual
