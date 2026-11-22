import tmp.sheaf.xif.paper.S2582P12ClosedActual

/-!
# S2585: the linear residue factor of the S2579 certificate polynomial at 613

Let `S2579P12` be the explicit monic integer polynomial of the Kummer-Dedekind
candidate `S2579Theta`, and let `S2582_P12Certificate` identify it with the
minimal polynomial of `S2579Theta`.  Reducing the coefficients of `S2579P12`
modulo 613 gives

  63 + 438 X^2 + 414 X^4 + 585 X^6 + 149 X^8 + 108 X^10 + X^12

(the residues, low to high, are 63, 0, 438, 0, 414, 0, 585, 0, 149, 0, 108, 0, 1).
The residue 21 is a root of this reduced polynomial, so the linear-factor input
`S2579LinearFactor613` of the S2579 Kummer-Dedekind reduction holds.

The coefficient reductions are proved by exhibiting each difference as a
multiple of 613 (`ZMod.intCast_zmod_eq_zero_iff_dvd`); the final evaluation is
the integer 9162940516966278 = 2 * 613^2, reduced by the same divisibility
criterion.  No axiom, `sorry`, `True`/PUnit gate, or `native_decide` is used.
-/

noncomputable section

set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2585LinearFactorActual

open LeanFormal.IUT.XiFPaper.S2579Kummer613Actual
open LeanFormal.IUT.XiFPaper.S2582P12ClosedActual

/-- The reduction of `S2579P12` modulo 613, in ascending order. -/
def S2585P12mod : (ZMod 613)[X] :=
  C 63 + C 438 * X ^ 2 + C 414 * X ^ 4 + C 585 * X ^ 6 + C 149 * X ^ 8 +
    C 108 * X ^ 10 + X ^ 12

/-- A coefficient congruent to `r` modulo 613 reduces to `r` in `ZMod 613`. -/
private theorem cast_eq_of_dvd (a : ℤ) (r : ℕ) (h : (613 : ℤ) ∣ a - r) :
    (Int.castRingHom (ZMod 613)) a = (r : ZMod 613) := by
  change ((a : ℤ) : ZMod 613) = (r : ZMod 613)
  have hz : ((a - (r : ℤ) : ℤ) : ZMod 613) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h
  push_cast at hz
  exact sub_eq_zero.mp hz

private theorem S2585_cast_0 :
    (Int.castRingHom (ZMod 613))
      (17461463173174011582761234456954928886602725098127406596813431452619322589360189151409387505478783853884785910317333751256475494692028676046849 : ℤ) =
      (63 : ZMod 613) :=
  cast_eq_of_dvd _ 63 (by norm_num)

private theorem S2585_cast_2 :
    (Int.castRingHom (ZMod 613))
      (52528898937498104220425280396744414010535592369189759840509931021767640039634491648742817305763558849812346150540279814 : ℤ) =
      (438 : ZMod 613) :=
  cast_eq_of_dvd _ 438 (by norm_num)

private theorem S2585_cast_4 :
    (Int.castRingHom (ZMod 613))
      (526670884064012082338601412686825197828814168607551341522761345584496744723849057857765220810767 : ℤ) =
      (414 : ZMod 613) :=
  cast_eq_of_dvd _ 414 (by norm_num)

private theorem S2585_cast_6 :
    (Int.castRingHom (ZMod 613))
      (997047820666501462053751168487623450855112506104272112674336787438501908 : ℤ) =
      (585 : ZMod 613) :=
  cast_eq_of_dvd _ 585 (by norm_num)

private theorem S2585_cast_8 :
    (Int.castRingHom (ZMod 613))
      (3795433823567007142194129160326239797448395456527 : ℤ) =
      (149 : ZMod 613) :=
  cast_eq_of_dvd _ 149 (by norm_num)

private theorem S2585_cast_10 :
    (Int.castRingHom (ZMod 613))
      (3686686718987773113532422 : ℤ) =
      (108 : ZMod 613) :=
  cast_eq_of_dvd _ 108 (by norm_num)

/-- Reduction of the certificate polynomial modulo 613. -/
theorem S2585_P12_map :
    S2579P12.map (Int.castRingHom (ZMod 613)) = S2585P12mod := by
  unfold S2579P12 S2585P12mod
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    Polynomial.map_X, Polynomial.map_one]
  rw [S2585_cast_0, S2585_cast_2, S2585_cast_4, S2585_cast_6, S2585_cast_8,
    S2585_cast_10]
  ring

/-- The residue 21 is a root of the reduced certificate polynomial. -/
theorem S2585_eval_21 : eval (21 : ZMod 613) S2585P12mod = 0 := by
  have hnum : ((9162940516966278 : ℤ) : ZMod 613) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num
  have hval : eval (21 : ZMod 613) S2585P12mod = (9162940516966278 : ZMod 613) := by
    norm_num [S2585P12mod]
  rw [hval]
  exact hnum

/-- `S2579LinearFactor613`: the minimal polynomial of `S2579Theta` has a root
modulo 613. -/
theorem S2585_linearFactor : S2579LinearFactor613 := by
  refine ⟨(21 : ZMod 613), ?_⟩
  unfold S2579minpolyMod
  rw [S2582_P12Certificate]
  show eval (21 : ZMod 613) (S2579P12.map (Int.castRingHom (ZMod 613))) = 0
  rw [S2585_P12_map]
  exact S2585_eval_21

#print axioms S2585_P12_map
#print axioms S2585_eval_21
#print axioms S2585_linearFactor

end LeanFormal.IUT.XiFPaper.S2585LinearFactorActual
