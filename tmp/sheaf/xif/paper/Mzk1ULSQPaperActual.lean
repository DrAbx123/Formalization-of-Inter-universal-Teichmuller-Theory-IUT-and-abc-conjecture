/- U-C: paper's s^Q object (IUT IV L1436-1501, david's extraction 2026-11-17).

Paper definitions (IV.txt):
  V(Q)^dst = {p : p | 2*3*5*l} union (image of Supp(qFtpd^ADiv + dFtpd^ADiv)) (L1455-1468);
  sF*^ADiv = Sum_{v in V(F*)^dst} e_v * v  (L1461-1484) with e_v the ramification index;
  for F* = Q every e_p = 1, hence
     s^Q = s^Q^ADiv = Sum_{p in V(Q)^dst} p, i.e. s^Q = Prod_{p in V(Q)^dst} p
  (DISTINCT rational primes, each multiplied once), and log s^Q = Sum log p (L1485-1501).

NOT the product over bad F-places with lift multiplicity: that repeats p once per
F-lift.  Also s^<= (coeffients log p with iota cutoff, L1485-1501) is a DIFFERENT
object; `paperLstarLogs` is only an upper bound for log s^<= (pi(x) log x), not an
equality.

OBLIGATION (not claimed here): log s^Q <= 2 d_mod S_ar + log(2*3*5*l), which needs
the per-fibre Prop 1.3(i) bounds on the q/d-support part (per-place dFtpd/fFtpd
data; currently only the global F letters exist).
-/
import tmp.sheaf.xif.paper.Mzk1ULBadFPrimeSetActual
import tmp.sheaf.xif.paper.Mzk1ULEModActual
import tmp.sheaf.xif.paper.Mzk1HT82AbsDifferentSumActual
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1ULBadFPrimeSetActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open LeanFormal.IUT.NumberFieldFinitePlace

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- rational primes in the support of the q-divisor (as distinct primes). -/
noncomputable def qSupportPrimes (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))] : Finset ℕ :=
  (badFPrimeSet T).image (fun P => (underIntGen (K := T.arithmetic.F) P).natAbs)

/-- rational primes in the ramified/different support of F. -/
noncomputable def dSupportPrimes (T : SourceNativeInitialThetaData l) : Finset ℕ :=
  (differentPlaces T.arithmetic.F).image (fun P => (underIntGen (K := T.arithmetic.F) P).natAbs)

/-- the special primes 2, 3, 5, l. -/
def specialPrimes (l : PrimeGeFive) : Finset ℕ := {2, 3, 5, l.value}

/-- paper's s^Q: primorial of the distinct rational primes in
V(Q)^dst = {p | 2*3*5*l} union Supp-image (IUT IV L1455-1501). -/
noncomputable def sQPaper (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))] : ℝ :=
  ∏ p ∈ (qSupportPrimes T ∪ dSupportPrimes T ∪ specialPrimes l), (p : ℝ)


/-- PROVED (generic): log of a product of nonzero naturals is the sum of the logs. -/
theorem log_prod_natCast_eq_sum (S : Finset ℕ) (hpos : ∀ p ∈ S, p ≠ 0) :
    Real.log (∏ p ∈ S, (p : ℝ)) = ∑ p ∈ S, Real.log (p : ℝ) := by
  rw [Real.log_prod]
  intro p hp
  exact_mod_cast hpos p hp

/-- PROVED: the special primes 2,3,5,l.value are nonzero. -/
theorem specialPrimes_ne_zero (p : ℕ) (hp : p ∈ specialPrimes l) : p ≠ 0 := by
  simp only [specialPrimes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · exact l.prime.ne_zero

/-- PROVED: the paper's log s^Q = Sum over V(Q)^dst of log p, given positivity of
the support primes (provable from `underIntGen_natAbs_ge_one`/differentPlaces; kept
as explicit hypotheses here, not paper conditions). -/
theorem log_sQPaper_eq_sum_log
    (hq : ∀ p ∈ qSupportPrimes T, p ≠ 0)
    (hd : ∀ p ∈ dSupportPrimes T, p ≠ 0) :
    Real.log (sQPaper T) =
      ∑ p ∈ (qSupportPrimes T ∪ dSupportPrimes T ∪ specialPrimes l),
        Real.log (p : ℝ) := by
  unfold sQPaper
  apply log_prod_natCast_eq_sum
  intro p hp
  rcases Finset.mem_union.mp hp with h | hs'
  · rcases Finset.mem_union.mp h with hq' | hd'
    · exact hq p hq'
    · exact hd p hd'
  · exact specialPrimes_ne_zero (l := l) p hs'

end LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual
end