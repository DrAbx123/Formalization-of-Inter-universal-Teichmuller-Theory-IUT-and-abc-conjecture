/- U-R C2 theta side: ball-ceil route setup (task-13, <= route) + old-corpus mapping.

Status (no sorry, no axiom): proved here are
* le_ceilExp : a <= ceilExp a for a >= 0 (ceilExp a = Int.ceil(a e)/e, the
  ceiling of a in the norm value group p^(-(1/e) Z));
* norm_prime_eq_inv : ||p|| = p^{-1};
* exists_norm_pow_eq_prime_zpow : for x != 0, ||x||^e = p^(-n) for some n : Z.

Retained target: BallCeilEqualityAt (norm ball of exponent a equals the ball at
ceilExp a).  Not assumed anywhere.

Old-corpus mapping (accepted ABCBridge layer, to be wired next, see team report):
* GlobalQVFamThetaHullScalarActual: oneSignedLabel / oneSignedLabel_gauss (the
  j = 1 label exists as an actual SignedLabel), qVFamLocalQPilotRegion /
  qVFamLocalThetaHull / their normalized log volumes,
  qVFamLocalQPilotRegion_subset_thetaHull,
  qVFamLocalQPilotLogVolume_le_thetaHull (measure monotonicity, actual proof),
  nativeBadLocalWeight_nonneg, globalQVFamQPilotLog_le_thetaHull.
* QVPilotThetaHullLatticeInclusionActual: qPilotRegion_eq_theta_one,
  qPilotRegion_subset_union, qPilotLog_eq_neg_sum, thetaHullLog_eq_neg_sum,
  qPilotLog_eq_thetaHullLog (q-pilot log = theta-hull log in the minimal sector,
  both = -(sum c) log p, under the fractional scaling datum).
* QVPilotThetaHullNestingActual: thetaRegion_subset_qPilot,
  thetaRegionUnion_subset_qPilot, qPilotLog_le_thetaHullLog.
* FinitePlaceStepVJInvariant.arithmeticTuple_stepV_hull_le_paperBound_of_jInvariant:
  accepted per-packet upper bound: there is an actual DVR-integer representative
  varpi (no completion 2l-root) with localNormOrder varpi = label^2*(-ord jValue)/(2l)
  and normalized hull log-volume <= the C1 paper bound
  (-label^2*(-ord jValue)/(2l) + sum different + 1) log p + exceptional sum.
* Mzk1ULPacketVActual: packetV / packetB / packetV_le_packetB / packetExceptional.
Together these suggest htheta (theta <= H_pkt) is wired from the accepted StepV
bound plus the q-pilot / theta-hull identification, rather than from the ball-ceil
formula; the ball-ceil lemmas above remain useful for the (<=) numerical side. -/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalAbsorption
import LeanFormal.IUT.Foundations.LocalFields.PadicFractionalLattice
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaHullUpperActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NumberFieldFinitePlace

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K] [NormedAlgebra ℚ_[p] K]

/-- The ceiling of a in the norm value group p^(-(1/e) Z): ceil(a e)/e. -/
noncomputable def ceilExp (a : ℝ) : ℝ :=
  (Int.ceil (a * (logShellRamificationExponent (K := K) (p := p) : ℝ)) : ℝ) /
    (logShellRamificationExponent (K := K) (p := p) : ℝ)

/-- The ceiling exponent is at least a for a >= 0. -/
theorem le_ceilExp {a : ℝ} (ha : 0 ≤ a) : a ≤ ceilExp (p := p) (K := K) a := by
  unfold ceilExp
  have he : (0 : ℝ) < (logShellRamificationExponent (K := K) (p := p) : ℝ) := by
    exact_mod_cast logShellRamificationExponent_pos (K := K) (p := p)
  have hceil : a * (logShellRamificationExponent (K := K) (p := p) : ℝ) ≤
      (Int.ceil (a * (logShellRamificationExponent (K := K) (p := p) : ℝ)) : ℝ) :=
    Int.le_ceil _
  rw [le_div_iff₀ he]
  exact hceil

/-- Norm of the rational prime in K: ||p|| = p^{-1}. -/
theorem norm_prime_eq_inv : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
  calc ‖(p : K)‖ = ‖algebraMap ℚ_[p] K (p : ℚ_[p])‖ := by
        rw [(map_natCast (algebraMap ℚ_[p] K) p).symm]
    _ = ‖(p : ℚ_[p])‖ := norm_algebraMap' _ _
    _ = (p : ℝ)⁻¹ := Padic.norm_p

/-- Norm values of nonzero elements: the e-th power of the norm is p^(-n) for
some integer n. -/
theorem exists_norm_pow_eq_prime_zpow {x : K} (hx : x ≠ 0) :
    ∃ n : ℤ, ‖x‖ ^ (logShellRamificationExponent (K := K) (p := p)) =
      (p : ℝ) ^ (-n) := by
  obtain ⟨n, hn⟩ :=
    LocalFieldLogarithm.exists_norm_pow_logShellRamificationExponent_eq_prime_zpow
      (K := K) (p := p) x hx
  refine ⟨n, ?_⟩
  rw [hn, show ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹ from Padic.norm_p, inv_zpow, zpow_neg]

/-- **Retained target (ball-ceil equality)**: the norm ball of exponent a >= 0
equals the norm ball at its value-group ceiling ceilExp a.  Not assumed
anywhere; its proof (read-off of the norm value group) is in progress. -/
def BallCeilEqualityAt (a : ℝ) : Prop :=
  padicFractionalLattice (p := p) (K := K) a =
    padicFractionalLattice (p := p) (K := K) (ceilExp (p := p) (K := K) a)

/-- Local ball-ceil equality via the value group: for a >= 0 the norm ball of
exponent a equals the norm ball of exponent Int.ceil(a e)/e (the ceiling in
p^(-(1/e) Z)). -/
theorem padicFractionalLattice_eq_intCeil {a : ℝ} (ha : 0 ≤ a) :
    padicFractionalLattice (p := p) (K := K) a =
      padicFractionalLattice (p := p) (K := K)
        ((Int.ceil (a * (logShellRamificationExponent (K := K) (p := p) : ℝ)) : ℝ) /
          (logShellRamificationExponent (K := K) (p := p) : ℝ)) := by
  set e : ℕ := logShellRamificationExponent (K := K) (p := p) with he_def
  have he_pos : 0 < e := logShellRamificationExponent_pos (K := K) (p := p)
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he_pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp1
  set k : ℤ := Int.ceil (a * (e : ℝ)) with hk_def
  have haa : a ≤ (k : ℝ) / (e : ℝ) := by
    rw [le_div_iff₀ heR]
    rw [hk_def]
    exact Int.le_ceil _
  have hceil_eq : ((k : ℝ) / (e : ℝ)) * (e : ℝ) = (k : ℝ) := by
    field_simp
  refine SetLike.ext ?_
  intro x
  rw [mem_padicFractionalLattice_iff, mem_padicFractionalLattice_iff]
  constructor
  · intro hx
    rcases eq_or_ne x 0 with rfl | hxne
    · simpa using Real.rpow_nonneg hp0.le (-((k : ℝ) / (e : ℝ)))
    · obtain ⟨n, hn⟩ := exists_norm_pow_eq_prime_zpow (p := p) (K := K) hxne
      rw [← he_def] at hn
      have hxpow_eq : ‖x‖ ^ e = (p : ℝ) ^ (-(n : ℝ)) := by
        rw [hn, ← Real.rpow_intCast]
        congr 1
        push_cast
        ring
      have hxpow_le_ae : ‖x‖ ^ e ≤ (p : ℝ) ^ (-(a * (e : ℝ))) := by
        calc ‖x‖ ^ e ≤ ((p : ℝ) ^ (-a)) ^ e := pow_le_pow_left₀ (norm_nonneg x) hx e
          _ = (p : ℝ) ^ (-(a * (e : ℝ))) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
              congr 1
              ring
      have hle : a * (e : ℝ) ≤ (n : ℝ) := by
        have hle' : (p : ℝ) ^ (-(n : ℝ)) ≤ (p : ℝ) ^ (-(a * (e : ℝ))) :=
          hxpow_eq ▸ hxpow_le_ae
        have hlog := Real.log_le_log (Real.rpow_pos_of_pos hp0 _) hle'
        rw [Real.log_rpow hp0, Real.log_rpow hp0] at hlog
        have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
        nlinarith [hlog, hlogp]
      have hkn : (k : ℝ) ≤ (n : ℝ) := by
        rw [hk_def]
        exact_mod_cast (Int.ceil_le.mpr hle)
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := le_trans (mul_nonneg ha heR.le) hle
      have he1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he_pos
      have hxpow_le : ‖x‖ ^ e ≤ (p : ℝ) ^ (-(k : ℝ)) := by
        rw [hxpow_eq]
        exact Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith [hkn])
      by_contra hcon
      push_neg at hcon
      have hlt_pow : ((p : ℝ) ^ (-((k : ℝ) / (e : ℝ)))) ^ e < ‖x‖ ^ e :=
        pow_lt_pow_left₀ hcon (Real.rpow_nonneg hp0.le _) he_pos.ne'
      have hleft : ((p : ℝ) ^ (-((k : ℝ) / (e : ℝ)))) ^ e =
          (p : ℝ) ^ (-(k : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
        congr 1
        rw [neg_mul, div_mul_cancel₀ _ heR.ne']
      rw [hleft] at hlt_pow
      exact absurd hlt_pow (not_lt.mpr hxpow_le)
  · intro hx
    have hle : (p : ℝ) ^ (-((k : ℝ) / (e : ℝ))) ≤ (p : ℝ) ^ (-a) := by
      apply Real.rpow_le_rpow_of_exponent_le hp1.le
      linarith [haa]
    exact hx.trans hle

#print axioms padicFractionalLattice_eq_intCeil
#print axioms le_ceilExp
#print axioms norm_prime_eq_inv
#print axioms exists_norm_pow_eq_prime_zpow

end LeanFormal.IUT.XiFPaper.Mzk1URThetaHullUpperActual
end