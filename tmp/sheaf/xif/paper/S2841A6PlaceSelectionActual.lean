import tmp.sheaf.xif.paper.S2847A6ArithmeticActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceSelection
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Ideal.GoingUp

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S2841A6PlaceSelectionActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- The rational prime ideal (37) in Z. -/
def S2841P : Ideal ℤ := Ideal.span {(37 : ℤ)}

instance : S2841P.IsPrime := by
  rw [S2841P, Ideal.span_singleton_prime (by norm_num : (37 : ℤ) ≠ 0)]
  exact (Nat.prime_iff_prime_int.mp (by norm_num : Nat.Prime 37))

instance : S2841P.IsMaximal :=
  Ideal.IsPrime.isMaximal (p := S2841P) (inferInstance : S2841P.IsPrime) (by
    rw [S2841P]
    exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (37 : ℤ) ≠ 0))


/-- A maximal ideal Q of O_{F6} lying over (37). -/
noncomputable def S2841Q : Ideal (NumberField.RingOfIntegers S2847F6) :=
  Classical.choose (Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (R := ℤ) (S := NumberField.RingOfIntegers S2847F6) S2841P)

theorem S2841Q_maximal :
    (S2841Q).IsMaximal :=
  (Classical.choose_spec (Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (R := ℤ) (S := NumberField.RingOfIntegers S2847F6) S2841P)).1

theorem S2841Q_liesOver : (S2841Q).LiesOver S2841P :=
  (Classical.choose_spec (Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (R := ℤ) (S := NumberField.RingOfIntegers S2847F6) S2841P)).2

/-- The finite place of F6 above 37. -/
noncomputable def S2841Place : NumberField.FinitePlace S2847A6.Fmod :=
  NumberField.FinitePlace.mk
    { asIdeal := S2841Q
      isPrime := S2841Q_maximal.isPrime
      ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField
        S2841Q_maximal (NumberField.RingOfIntegers.not_isField S2847F6) }

/-- 37 lies in Q, hence the residue characteristic is 37. -/
theorem S2841_thirtyseven_mem : ((37 : ℕ) : NumberField.RingOfIntegers S2847F6) ∈ S2841Q := by
  have hspan : (37 : ℤ) ∈ S2841P := Ideal.mem_span_singleton_self _
  have hunder : (37 : ℤ) ∈ S2841Q.under ℤ :=
    S2841Q_liesOver.over.le hspan
  simpa [Ideal.under_def, S2841P] using hunder

theorem S2841_residueCharacteristic :
    residueCharacteristic S2841Place = 37 := by
  unfold NumberFieldFinitePlace.residueCharacteristic
  haveI : S2841Q.IsMaximal := S2841Q_maximal
  haveI : Field (NumberField.RingOfIntegers S2847F6 ⧸ S2841Q) :=
    Ideal.Quotient.field S2841Q
  unfold S2841Place
  change ringChar (NumberField.RingOfIntegers S2847A6.F ⧸
    (NumberField.FinitePlace.mk
      { asIdeal := S2841Q
        isPrime := S2841Q_maximal.isPrime
        ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField
          S2841Q_maximal (NumberField.RingOfIntegers.not_isField S2847F6) }).maximalIdeal.asIdeal) = 37
  rw [NumberField.FinitePlace.maximalIdeal_mk]
  haveI : S2841Q.IsMaximal := S2841Q_maximal
  haveI : Nontrivial (NumberField.RingOfIntegers S2847F6 ⧸ S2841Q) :=
    Submodule.Quotient.nontrivial_iff.mpr (Ideal.IsMaximal.ne_top S2841Q_maximal)
  exact CharP.ringChar_of_prime_eq_zero (by norm_num : Nat.Prime 37)
    ((map_natCast (Ideal.Quotient.mk S2841Q) 37).symm.trans
      (Ideal.Quotient.eq_zero_iff_mem.mpr S2841_thirtyseven_mem))

/-- The A6 selected-place record: one 37-place. -/
noncomputable def S2841PlaceSelection : SourcePlaceSelection S2847A6 where
  V_mod_bad := {S2841Place}
  V_mod_bad_odd_residue_characteristic := by
    intro p hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    rw [S2841_residueCharacteristic]
    exact ⟨18, by norm_num⟩
  V_mod_bad_nonempty := ⟨S2841Place, by simp⟩

#check S2841Place
#check S2841PlaceSelection
#print axioms S2841PlaceSelection

end LeanFormal.IUT.XiFPaper.S2841A6PlaceSelectionActual
end
