/- U-C paper letters (de-conditionalization): actual definition of d_mod.

route IUT IV L1259-1262: d_mod := [F_mod : Q] (an integer >= 1).  This file defines
the actual d_mod from the number-field degree and proves the paper bound 1 <= d_mod,
so the retained `hd_mod` hypothesis of the Step(viii) structure can be replaced by
this proved theorem.  (Note: A511ExplicitConstantGlueActual.hdmod is a paper-parameter
FIELD, not an actual proof; it is not used here.)
-/
import tmp.sheaf.xif.paper.Mzk1ULHpktActual
import tmp.sheaf.xif.paper.Mzk1UCHpktActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalDifferent
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.Mzk1ULBadFPrimeSetActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)

/-- actual d_mod := [F_mod : Q] as a real number (IUT IV L1259-1261). -/
noncomputable def dMod : ℝ := (Module.finrank ℚ T.arithmetic.Fmod : ℝ)

/-- paper bound (1 <=) d_mod (IUT IV L1262): the field F_mod is non-trivial. -/
theorem one_le_dMod : 1 ≤ dMod T := by
  unfold dMod
  have hpos : 0 < Module.finrank ℚ T.arithmetic.Fmod := Module.finrank_pos
  exact_mod_cast hpos


/-- (1 <=) the root discriminant of a number field: |disc K| >= 1 (nonzero integer)
and the exponent 1/finrank is nonnegative. -/
theorem one_le_rootDiscr (K : Type*) [Field K] [NumberField K] :
    1 ≤ NumberField.rootDiscr K := by
  rw [NumberField.rootDiscr_def]
  have hpos : (0 : ℤ) < |NumberField.discr K| :=
    abs_pos.mpr (NumberField.discr_ne_zero K)
  have hdisc_int : (1 : ℤ) ≤ |NumberField.discr K| := by omega
  have hdisc : (1 : ℝ) ≤ ((|NumberField.discr K| : ℤ) : ℝ) := by
    exact_mod_cast hdisc_int
  exact Real.one_le_rpow hdisc (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- degree-normalized log of the actual different (root discriminant),
route IUT IV L1294-1348 / L1362-1385 letters (log root discriminant). -/
noncomputable def logDifferentF (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.log (NumberField.rootDiscr K)

/-- PROVED: the normalized log-different is nonnegative. -/
theorem zero_le_logDifferentF (K : Type*) [Field K] [NumberField K] :
    0 ≤ logDifferentF K :=
  Real.log_nonneg (one_le_rootDiscr K)

/-- degree-normalized log of the conductor supported on the finite prime set S
(paper f_F side; the paper conductor has coefficient 1 on its support). -/
noncomputable def logConductorF (K : Type*) [Field K] [NumberField K]
    (S : Finset ℕ) : ℝ :=
  (∑ p ∈ S, Real.log (p : ℝ)) / (Module.finrank ℚ K : ℝ)

/-- PROVED: the normalized log-conductor is nonnegative when the primes in S are >= 2. -/
theorem zero_le_logConductorF (K : Type*) [Field K] [NumberField K]
    (S : Finset ℕ) (hprime : ∀ p ∈ S, 2 ≤ p) :
    0 ≤ logConductorF K S := by
  unfold logConductorF
  have hsum : 0 ≤ ∑ p ∈ S, Real.log (p : ℝ) := by
    apply Finset.sum_nonneg
    intro p hp
    have hp2 : (2 : ℕ) ≤ p := hprime p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast le_trans (by norm_num : (1:ℕ) ≤ 2) hp2
    exact Real.log_nonneg hp1
  have hfr : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  exact div_nonneg hsum hfr.le

/-- S_ar = log d_F + log f_F (paper L1362-1385), degree-normalized. -/
noncomputable def SAr (K : Type*) [Field K] [NumberField K] (S : Finset ℕ) : ℝ :=
  logDifferentF K + logConductorF K S

/-- PROVED: S_ar is nonnegative (both summands are). -/
theorem zero_le_SAr (K : Type*) [Field K] [NumberField K]
    (S : Finset ℕ) (hprime : ∀ p ∈ S, 2 ≤ p) :
    0 ≤ SAr K S :=
  add_nonneg (zero_le_logDifferentF K) (zero_le_logConductorF K S hprime)


/-- actual bad-prime set: the set of rational primes underlying the bad places. -/
noncomputable def badPrimeSet (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Finset ℕ :=
  Finset.univ.image (fun b : Bad (nativePlaceSelection T) =>
    LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorP T b)

/-- PROVED: every bad prime is at least 2 (prime-ness via the qVFam prime instance). -/
theorem two_le_badPrimeSet (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (p : ℕ) (hp : p ∈ badPrimeSet T) : 2 ≤ p := by
  unfold badPrimeSet at hp
  rcases Finset.mem_image.mp hp with ⟨b, _, rfl⟩
  exact (LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorPFact T b).out.two_le

/-- S_ar on the actual tripodal-side field (route L1362-1385): paper log d_F plus the
paper-normalized conductor log f_F (place-weighted; IUT-TEXT L1309-1313/L1341-1353 +
Def 1.9).  The conductor is david's canonical
`Mzk1ULBadFPrimeSetActual.logConductorFActual` (full bad fiber, inertia-degree weight).
The old `SAr T.arithmetic.F (badPrimeSet T)` (prime-counted conductor) is SUPERSEDED
and kept below for historical reference only. -/
noncomputable def SAr_tripodal (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : ℝ :=
  logDifferentF T.arithmetic.F
    + LeanFormal.IUT.XiFPaper.Mzk1ULBadFPrimeSetActual.logConductorFActual T

/-- PROVED: S_ar (paper-faithful, /finrank normalized) is nonnegative. -/
theorem zero_le_SAr_tripodal (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] :
    0 ≤ SAr_tripodal T := by
  unfold SAr_tripodal
  exact add_nonneg (zero_le_logDifferentF T.arithmetic.F)
    (LeanFormal.IUT.XiFPaper.Mzk1ULBadFPrimeSetActual.zero_le_logConductorFActual T)


/-- Actual log-different of the top field K (route L1294-1348, /finrank
normalized).  This is the concrete letter on the hlogdK side. -/
noncomputable def logDifferentK (T : SourceNativeInitialThetaData.{0} l) : ℝ :=
  logDifferentF T.arithmetic.K

/-- PROVED: the actual log-different of K is nonnegative. -/
theorem zero_le_logDifferentK (T : SourceNativeInitialThetaData.{0} l) :
    0 ≤ logDifferentK T :=
  zero_le_logDifferentF T.arithmetic.K

/-- Actual S_ar-like letter on K (log different of K plus the bad-prime conductor),
used as the comparison side for hlogdK. -/
noncomputable def SAr_K (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : ℝ :=
  SAr T.arithmetic.K (badPrimeSet T)

/-- PROVED: the K-side S_ar letter is nonnegative. -/
theorem zero_le_SAr_K (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : 0 ≤ SAr_K T := by
  unfold SAr_K
  exact zero_le_SAr T.arithmetic.K (badPrimeSet T) (fun p hp => two_le_badPrimeSet T p hp)

end LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
end