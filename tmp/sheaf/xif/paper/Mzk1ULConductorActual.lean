/- U-C: paper-faithful conductor letter for S_ar (route object correction).

Paper (IUT-TEXT/IV): fF^ADiv is the place divisor with support Supp(q^ADiv) and all
coefficients 1 (L1309-1313, L1341-1353), log(fF) = deg(fF^ADiv) with
deg(a) = (1/[F:Q]) Sum_v c_v log q_v (Def 1.9, L1206-1235); for v | p,
log q_v = f_v log p.  Hence log fF = (1/[F:Q]) Sum_{v in V(F)^bad} f_v log p_v,
i.e. the conductor letter carries the INERTIA DEGREE weight (not just 1 per
rational prime).  The old `Mzk1ULPaperLettersActual.logConductorF` (sum of log p
over primes divided by the degree) is SUPERSEDED and kept only for history.

IMPORTANT (david's spec check 2026-11-17): the bad F-places are NOT the single
lifts `nativeBadToFPlace b`; every bad Fmod place v has several F-places over it
(V(F)^bad = V^bad_mod x_{V_mod} V(F), IUT-TEXT L1305-1308).  So we work at the
ideal level: for each bad b, take ALL primes over b.1 in O_F via
`IsDedekindDomain.primesOverFinset` (Mathlib RingTheory/RamificationInertia/Basic:586)
and form their union.
-/
import tmp.sheaf.xif.paper.Mzk1ULPaperLettersActual
import tmp.sheaf.xif.paper.Mzk1HT82UnderIntGenQVActual
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULConductorActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- PROVED: for any ideal P, the conductor summand f_P log p_P is nonnegative.
(If the underlying rational prime is 0 the log is 0 in Lean; otherwise it is
positive.) -/
theorem conductorSummand_nonneg (P : Ideal (NumberField.RingOfIntegers T.arithmetic.F)) :
    0 ≤ (P.inertiaDeg ℤ : ℝ)
      * Real.log ((LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual.underIntGen P).natAbs : ℝ) := by
  have hinertia : (0 : ℝ) ≤ (P.inertiaDeg ℤ : ℝ) := by
    exact_mod_cast Nat.zero_le _
  rcases Nat.eq_zero_or_pos
      (LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual.underIntGen P).natAbs with h | h
  · rw [h]
    simp
  · have hlog : 0 ≤ Real.log
        ((LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual.underIntGen P).natAbs : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast h
    exact mul_nonneg hinertia hlog

/-- all F-primes over the bad moduli places (paper V(F)^bad), at ideal level. -/
noncomputable def badFPrimeSet : Finset (Ideal (NumberField.RingOfIntegers T.arithmetic.F)) :=
  (Finset.univ : Finset (Bad (nativePlaceSelection T))).biUnion
    (fun b => IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal)
      (NumberField.RingOfIntegers T.arithmetic.F))

/-- paper-normalized log conductor of F: (1/[F:Q]) Sum_{v in V(F)^bad} f_v log p_v. -/
noncomputable def logConductorFActual : ℝ :=
  (∑ P ∈ badFPrimeSet T,
      ((P.inertiaDeg ℤ : ℝ)
        * Real.log ((LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual.underIntGen P).natAbs : ℝ)))
    / (Module.finrank ℚ T.arithmetic.F : ℝ)

/-- PROVED: the paper-normalized conductor of F is nonnegative. -/
theorem logConductorFActual_nonneg : 0 ≤ logConductorFActual T := by
  unfold logConductorFActual
  have hsum : 0 ≤ ∑ P ∈ badFPrimeSet T,
      ((P.inertiaDeg ℤ : ℝ)
        * Real.log ((LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual.underIntGen P).natAbs : ℝ)) := by
    apply Finset.sum_nonneg
    intro P _
    exact conductorSummand_nonneg T P
  have hfr : (0 : ℝ) < (Module.finrank ℚ T.arithmetic.F : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := T.arithmetic.F)
  exact div_nonneg hsum hfr.le

/-- paper-faithful S_ar letter: root-discriminant log-different plus the
place-weighted conductor (paper L1365-1376, L1412-1426). -/
noncomputable def SAr_tripodal_paper : ℝ :=
  logDifferentF T.arithmetic.F + logConductorFActual T

/-- PROVED: S_ar (paper-faithful form) is nonnegative. -/
theorem zero_le_SAr_tripodal_paper : 0 ≤ SAr_tripodal_paper T := by
  unfold SAr_tripodal_paper
  exact add_nonneg (zero_le_logDifferentF T.arithmetic.F)
    (logConductorFActual_nonneg T)

end LeanFormal.IUT.XiFPaper.Mzk1ULConductorActual
end