import tmp.sheaf.xif.paper.S467KrootOrderControlAuditActual
import Mathlib.Algebra.Group.Int.TypeTags

/-!
# S1281: K-side 2l-root in the completion --- exact order obstruction

Consumer: S1272 / `S438QVFamilyKSideCandidateActual.KSideTwoLRootData`,
whose first field `root : Completion (qVFamilyKLift T b)` is still not
constructed.

This file does **not** construct a root in the completion and does not
introduce a weak `Nonempty` gate.  It proves the first exact consequence of
such a root, together with the resulting refutation when the consequence
fails:

* `FinitePlaceQCandidate.order_dvd_of_pow_eq`:
  if a nonzero q-candidate is an n-th power in its completion, then
  `n ∣ order`;
* `candidateKRootInCompletion_twoL_dvd_order`:
  the S1272 field `root_in_completion` implies
  `(2 * l) ∣ (qVFamilyK T b).order`;
* `ksideTwoLRootData_twoL_dvd_order`:
  any actual `KSideTwoLRootData` implies the same divisibility;
* `ksideTwoLRootData_l_dvd_ramification`:
  any actual root therefore forces `l ∣ qVFamilyKRamificationIdx` (S467).

Equivalently, if `(2 * l)` does not divide `(qVFamilyK T b).order`, the
chosen algebraic-closure root is not in the completion image, no completion
2l-th root exists, and `KSideTwoLRootData` is empty.  The residual arithmetic
gap is exactly whether `(2l) ∣ order_K` (which, since `l ∤ order_F`, requires
`l ∣ e`) and, after that valuation condition, whether the unit part is a
2l-th power; S467/S472 record that these inputs are not derived.  They are not
assumed here.  The ratio criterion below isolates the remaining root-of-unity
ambiguity once a completion root is known.

No `sorry`, no axiom, no arbitrary root.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceQCandidate

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {place : NumberField.FinitePlace K}

/-- If a nonzero q-candidate is an n-th power in its completion, then `n`
divides its positive discrete order.

The proof is the valuation argument: applying the discrete valuation to
`x ^ n = q` gives `v q = (v x) ^ n`; the additive exponent of `v q` is
therefore `n` times an integer, and positivity identifies the natural order
with that product. -/
theorem order_dvd_of_pow_eq (parameter : FinitePlaceQCandidate place)
    {x : Completion place} {n : Nat} (hn : 0 < n)
    (hx : x ^ n = parameter.q) :
    n ∣ parameter.order := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hx
    exact parameter.q_ne_zero hx.symm
  have hvx : (Valued.v x : WithZero (Multiplicative Int)) ≠ 0 := by
    intro h
    have hq : (Valued.v parameter.q : WithZero (Multiplicative Int)) = 0 := by
      rw [← hx, map_pow, h, zero_pow hn.ne']
    exact parameter.valuation_ne_zero hq
  have hunzero :
      WithZero.unzero parameter.valuation_ne_zero =
        WithZero.unzero hvx ^ n := by
    apply WithZero.coe_injective
    simp only [WithZero.coe_unzero, WithZero.coe_pow]
    rw [← hx, map_pow]
  let b : Int := -Multiplicative.toAdd (WithZero.unzero hvx)
  have hexp : parameter.exponent = b * (n : Int) := by
    dsimp [b]
    rw [exponent, hunzero, Int.toAdd_pow]
    ring
  have hbpos : 0 < b := by
    have hbn : 0 < b * (n : Int) := by
      rw [← hexp]
      exact parameter.exponent_pos
    have hnint : (0 : Int) < n := by exact_mod_cast hn
    nlinarith
  have horder : parameter.order = b.toNat * n := by
    rw [order, hexp, Int.toNat_mul (le_of_lt hbpos)
      (by exact_mod_cast le_of_lt hn)]
    simp
  exact ⟨b.toNat, by rw [horder, Nat.mul_comm]⟩

end LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceQCandidate

namespace LeanFormal.IUT.XiFPaper.S1281KSideRootCompletionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceQCandidate
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open LeanFormal.IUT.XiFPaper.S459KrootCandidateActual
open LeanFormal.IUT.XiFPaper.S467KrootOrderControlAuditActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The exact S1272 `root_in_completion`: the chosen algebraic-closure root
of `qVFamilyK` lies in the image of the completion. -/
def candidateKRootInCompletion : Prop :=
  candidateKRoot T b ∈ Set.range (algebraMap (Kq T b) (ACq T b))

/-- The same condition unpacked. -/
theorem candidateKRootInCompletion_iff :
    candidateKRootInCompletion T b ↔
      ∃ x : Kq T b,
        algebraMap (Kq T b) (ACq T b) x = candidateKRoot T b :=
  Iff.rfl

/-- Existence of an actual 2l-th root of `qVFamilyK` in the completion. -/
def completionTwoLRoot : Prop :=
  ∃ x : Kq T b, x ^ (2 * l.value) = (qVFamilyK T b).q

/-- A completion element with the prescribed 2l-th power is nonzero. -/
theorem completionRoot_ne_zero {x : Kq T b}
    (hx : x ^ (2 * l.value) = (qVFamilyK T b).q) : x ≠ 0 := by
  rintro rfl
  rw [zero_pow (Nat.mul_pos (by norm_num) l.prime.pos).ne'] at hx
  exact (qVFamilyK T b).q_ne_zero hx.symm

/-- For any nonzero completion element `x`, the chosen algebraic-closure
candidate lies in the completion image iff the ratio
`candidateKRoot / x` does.  This isolates the remaining root-of-unity
ambiguity from the order obstruction. -/
theorem candidateKRootInCompletion_iff_ratio_mem
    (x : Kq T b) (hx : x ≠ 0) :
    candidateKRootInCompletion T b ↔
      (candidateKRoot T b / algebraMap (Kq T b) (ACq T b) x) ∈
        Set.range (algebraMap (Kq T b) (ACq T b)) := by
  have hmapx0 : algebraMap (Kq T b) (ACq T b) x ≠ 0 :=
    (map_ne_zero (algebraMap (Kq T b) (ACq T b))).mpr hx
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y / x, ?_⟩
    rw [map_div₀, hy]
  · rintro ⟨z, hz⟩
    refine ⟨x * z, ?_⟩
    rw [map_mul, hz]
    field_simp [hmapx0]

/-- The ratio of `candidateKRoot` by an actual completion 2l-th root is a
2l-th root of unity. -/
theorem candidateKRoot_div_completionRoot_pow_eq_one
    (x : Kq T b) (hx : x ^ (2 * l.value) = (qVFamilyK T b).q) :
    (candidateKRoot T b / algebraMap (Kq T b) (ACq T b) x) ^
        (2 * l.value) = 1 := by
  have hq0 : algebraMap (Kq T b) (ACq T b) ((qVFamilyK T b).q) ≠ 0 :=
    (map_ne_zero (algebraMap (Kq T b) (ACq T b))).mpr
      (qVFamilyK T b).q_ne_zero
  rw [div_pow, ← map_pow, hx]
  rw [show candidateKRoot T b ^ (2 * l.value) =
      algebraMap (Kq T b) (ACq T b) ((qVFamilyK T b).q) by
        simpa [n2l] using candidateKRoot_pow T b]
  exact div_self hq0

/-- A completion element mapping to `candidateKRoot` is an actual 2l-th root
of `qVFamilyK` in the completion. -/
theorem completionTwoLRoot_of_candidateKRootInCompletion
    (h : candidateKRootInCompletion T b) : completionTwoLRoot T b := by
  rw [candidateKRootInCompletion_iff] at h
  obtain ⟨x, hx⟩ := h
  refine ⟨x, ?_⟩
  apply (algebraMap (Kq T b) (ACq T b)).injective
  calc
    algebraMap (Kq T b) (ACq T b) (x ^ (2 * l.value))
        = (algebraMap (Kq T b) (ACq T b) x) ^ (2 * l.value) := by
          rw [map_pow]
    _ = candidateKRoot T b ^ (2 * l.value) := by rw [hx]
    _ = algebraMap (Kq T b) (ACq T b) ((qVFamilyK T b).q) := by
          simpa [n2l] using candidateKRoot_pow T b

/-- Any actual 2l-th root in the completion forces divisibility of the
`qVFamilyK` order. -/
theorem completionTwoLRoot_twoL_dvd_order
    (h : completionTwoLRoot T b) :
    (2 * l.value) ∣ (qVFamilyK T b).order := by
  obtain ⟨x, hx⟩ := h
  exact order_dvd_of_pow_eq (qVFamilyK T b)
    (n := 2 * l.value) (Nat.mul_pos (by norm_num) l.prime.pos) hx

/-- The exact S1272 first field implies the order control:
`root_in_completion -> (2l) | order_K`. -/
theorem candidateKRootInCompletion_twoL_dvd_order
    (h : candidateKRootInCompletion T b) :
    (2 * l.value) ∣ (qVFamilyK T b).order :=
  completionTwoLRoot_twoL_dvd_order T b
    (completionTwoLRoot_of_candidateKRootInCompletion T b h)

/-- Any inhabited `KSideTwoLRootData` forces `(2l) | order_K`. -/
theorem ksideTwoLRootData_twoL_dvd_order
    (D : KSideTwoLRootData T b) :
    (2 * l.value) ∣ (qVFamilyK T b).order :=
  order_dvd_of_pow_eq (qVFamilyK T b)
    (n := 2 * l.value) (Nat.mul_pos (by norm_num) l.prime.pos) D.root_pow

/-- Any actual completion 2l-th root forces `l` to divide the K-side local
ramification index (the order factorization of S438/S467). -/
theorem completionTwoLRoot_l_dvd_ramification
    (h : completionTwoLRoot T b) :
    l.value ∣ qVFamilyKRamificationIdx T b :=
  twoL_dvd_order_K_requires_ramification T b
    (completionTwoLRoot_twoL_dvd_order T b h)

/-- `root_in_completion` forces `l ∣ qVFamilyKRamificationIdx`. -/
theorem candidateKRootInCompletion_l_dvd_ramification
    (h : candidateKRootInCompletion T b) :
    l.value ∣ qVFamilyKRamificationIdx T b :=
  twoL_dvd_order_K_requires_ramification T b
    (candidateKRootInCompletion_twoL_dvd_order T b h)

/-- Any inhabited `KSideTwoLRootData` forces `l ∣ qVFamilyKRamificationIdx`. -/
theorem ksideTwoLRootData_l_dvd_ramification
    (D : KSideTwoLRootData T b) :
    l.value ∣ qVFamilyKRamificationIdx T b :=
  twoL_dvd_order_K_requires_ramification T b
    (ksideTwoLRootData_twoL_dvd_order T b D)

/-! ### Refutations from the exact arithmetic obstruction -/

/-- If `(2l)` does not divide `order_K`, the chosen algebraic-closure root is
not in the completion image. -/
theorem candidateKRoot_notInCompletion_of_not_dvd
    (h : ¬ (2 * l.value) ∣ (qVFamilyK T b).order) :
    ¬ candidateKRootInCompletion T b :=
  fun hroot => h (candidateKRootInCompletion_twoL_dvd_order T b hroot)

/-- If `(2l)` does not divide `order_K`, there is no actual completion 2l-th
root of `qVFamilyK`. -/
theorem not_completionTwoLRoot_of_not_dvd
    (h : ¬ (2 * l.value) ∣ (qVFamilyK T b).order) :
    ¬ completionTwoLRoot T b :=
  fun hroot => h (completionTwoLRoot_twoL_dvd_order T b hroot)

/-- If `(2l)` does not divide `order_K`, `KSideTwoLRootData` has no
inhabitant. -/
theorem not_ksideTwoLRootData_of_not_dvd
    (h : ¬ (2 * l.value) ∣ (qVFamilyK T b).order) :
    ¬ Nonempty (KSideTwoLRootData T b) := by
  rintro ⟨D⟩
  exact h (ksideTwoLRootData_twoL_dvd_order T b D)

/-- If `l` does not divide the K-side local ramification index, the chosen
algebraic-closure root is not in the completion image. -/
theorem candidateKRoot_notInCompletion_of_l_not_dvd_ramification
    (h : ¬ l.value ∣ qVFamilyKRamificationIdx T b) :
    ¬ candidateKRootInCompletion T b :=
  fun hroot => h (candidateKRootInCompletion_l_dvd_ramification T b hroot)

/-- If `l` does not divide the K-side local ramification index, there is no
actual completion 2l-th root of `qVFamilyK`. -/
theorem not_completionTwoLRoot_of_l_not_dvd_ramification
    (h : ¬ l.value ∣ qVFamilyKRamificationIdx T b) :
    ¬ completionTwoLRoot T b :=
  fun hroot => h (completionTwoLRoot_l_dvd_ramification T b hroot)

/-- If `l` does not divide the K-side local ramification index,
`KSideTwoLRootData` has no inhabitant. -/
theorem not_ksideTwoLRootData_of_l_not_dvd_ramification
    (h : ¬ l.value ∣ qVFamilyKRamificationIdx T b) :
    ¬ Nonempty (KSideTwoLRootData T b) := by
  rintro ⟨D⟩
  exact h (ksideTwoLRootData_l_dvd_ramification T b D)

#check order_dvd_of_pow_eq
#check candidateKRootInCompletion
#check candidateKRootInCompletion_iff
#check completionTwoLRoot
#check completionRoot_ne_zero
#check candidateKRootInCompletion_iff_ratio_mem
#check candidateKRoot_div_completionRoot_pow_eq_one
#check completionTwoLRoot_of_candidateKRootInCompletion
#check completionTwoLRoot_twoL_dvd_order
#check candidateKRootInCompletion_twoL_dvd_order
#check ksideTwoLRootData_twoL_dvd_order
#check completionTwoLRoot_l_dvd_ramification
#check candidateKRootInCompletion_l_dvd_ramification
#check ksideTwoLRootData_l_dvd_ramification
#check candidateKRoot_notInCompletion_of_not_dvd
#check not_completionTwoLRoot_of_not_dvd
#check not_ksideTwoLRootData_of_not_dvd
#check candidateKRoot_notInCompletion_of_l_not_dvd_ramification
#check not_completionTwoLRoot_of_l_not_dvd_ramification
#check not_ksideTwoLRootData_of_l_not_dvd_ramification

end LeanFormal.IUT.XiFPaper.S1281KSideRootCompletionActual
