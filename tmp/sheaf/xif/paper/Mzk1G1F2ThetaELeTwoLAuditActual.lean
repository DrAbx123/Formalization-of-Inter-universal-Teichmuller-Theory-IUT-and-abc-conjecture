/- AUDIT: can `he : e <= 2l` be PROVED from the relative-ramification/degree reading?

  Relative reading: e is the ramification index of K_w / F_P, and K_w / F_P is the actual
  2l-th root (Kummer) extension, so [K_w : F_P] divides 2l and in particular
  `e <= [K_w : F_P] = 2l` by `Ideal.ramificationIdx_le_finrank` (Mathlib).

  THIS FILE records the exact arithmetic reduction (proved, no sorry):
    `e_le_twoL_of_le_finrank {N e : Nat} (hN : (N:Real) = 2*l) (he : e <= N) :
       (e:Real) <= 2*l`
  and the missing DEGREE input as an explicit Prop `ThetaRelativeDegreeInput`.
  NO tree donor proves `Module.finrank (F_P) K_w = 2*l` (or any relative degree formula
  for the 2l-th root completion); `Ideal.ramificationIdx_le_finrank` only gives
  `ramificationIdx <= Module.finrank` once the relative finrank is known.
  No stub, no sorry/axiom. -/
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaELeTwoLAuditActual

/-- Relative-ramification reading of `he`: `e <= 2l` follows from `e <= N = 2l`. -/
theorem e_le_twoL_of_le_finrank {l : LeanFormal.IUT.PrimeGeFive} {N e : ℕ}
    (hN : (N : ℝ) = 2 * (l.value : ℝ)) (he : e ≤ N) :
    (e : ℝ) ≤ 2 * (l.value : ℝ) := by
  rw [← hN]
  exact_mod_cast he

/-- The missing DEGREE input for `he`: the relative degree of the actual 2l-th root
    completion `K_w / F_P` equals `2*l`.  No tree donor currently proves this. -/
def ThetaRelativeDegreeInput (K_w F_P : Type*) [Field K_w] [Field F_P]
    [Algebra F_P K_w] (l : LeanFormal.IUT.PrimeGeFive) : Prop :=
  Module.finrank F_P K_w = 2 * l.value

/-- Given the (missing) relative degree input and the relative ramification inequality
    `e <= [K_w : F_P]`, `he` follows.  The inequality is `Ideal.ramificationIdx_le_finrank`
    in the Dedekind-domain setting; the degree identity is the missing donor. -/
theorem e_le_twoL_of_relative_degree {l : LeanFormal.IUT.PrimeGeFive}
    {N e : ℕ} (hN : (N : ℝ) = 2 * (l.value : ℝ)) (he : e ≤ N) :
    (e : ℝ) ≤ 2 * (l.value : ℝ) := e_le_twoL_of_le_finrank hN he

#print axioms e_le_twoL_of_le_finrank
#print axioms e_le_twoL_of_relative_degree

end LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaELeTwoLAuditActual
