import Mathlib
import tmp.sheaf.xif.paper.S2485Places3Actual
import tmp.sheaf.xif.paper.S2482QiArithmeticActual

noncomputable section
open scoped NumberField
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2485Places3Actual

namespace LeanFormal.IUT.XiFPaper.S2486PlacesActual

local instance S2486IsPrime : (Ideal.span {(3 : ℤ)}).IsPrime := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (Int.ideal_span_isMaximal_of_prime 3).isPrime

noncomputable def P0 : {P // P ∈ (Ideal.span {(3 : ℤ)}).primesOver (𝓞 F)} :=
  Classical.choice (Ideal.nonempty_primesOver (Ideal.span {(3 : ℤ)}))

theorem P0_mem : P0.1 ∈ (Ideal.span {(3 : ℤ)}).primesOver (𝓞 F) := P0.2

theorem P0_ne_bot : P0.1 ≠ ⊥ :=
  Ideal.ne_bot_of_mem_primesOver (p := Ideal.span {(3 : ℤ)})
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (3 : ℤ) ≠ 0)) P0_mem

def v0 : IsDedekindDomain.HeightOneSpectrum (𝓞 F) where
  asIdeal := P0.1
  isPrime := P0_mem.1
  ne_bot := P0_ne_bot

def q0 : NumberField.FinitePlace F := NumberField.FinitePlace.mk v0

def V : Set (NumberField.FinitePlace F) := {q0}

theorem V_nonempty : V.Nonempty := ⟨q0, rfl⟩

theorem P0_under : P0.1.under ℤ = Ideal.span {(3 : ℤ)} :=
  (Ideal.over_def (p := Ideal.span {(3 : ℤ)}) (P := P0.1)).symm

noncomputable def S2486Section :
    {q // q ∈ S2485VModBad} ≃ {q // q ∈ V} where
  toFun _ := ⟨q0, by simp [V]⟩
  invFun _ := ⟨S2485p3, by simp [S2485VModBad]⟩
  left_inv x := by
    apply Subtype.ext
    exact (Set.mem_singleton_iff.mp x.2).symm
  right_inv x := by
    apply Subtype.ext
    exact (Set.mem_singleton_iff.mp x.2).symm

#print axioms P0_under
#print axioms P0_ne_bot
#print axioms S2486Section

end LeanFormal.IUT.XiFPaper.S2486PlacesActual
end