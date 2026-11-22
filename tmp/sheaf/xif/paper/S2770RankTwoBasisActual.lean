import tmp.sheaf.xif.paper.S2769ProjAffineCardActual
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Free

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2770RankTwoBasisActual

open WeierstrassCurve
open LeanFormal.IUT.XiFPaper.S2769ProjAffineCardActual

local instance S2770FactFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K] [IsAlgClosed K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Projective E[5] is a 2-dimensional ZMod-5 vector space. -/
theorem S2770_finrank :
    Module.finrank (ZMod 5)
      (AddSubgroup.torsionBy W.toProjective.Point ((5 : ℕ) : ℤ)) = 2 := by
  let V := AddSubgroup.torsionBy W.toProjective.Point ((5 : ℕ) : ℤ)
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card V = 25 := by
    simpa [V] using S2769_projective_fiveTorsion_card W
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Module.Finite (ZMod 5) V := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod 5) (V := V)
  rw [hcard, Nat.card_zmod] at h
  have h2 : (5 : ℕ) ^ 2 = 5 ^ Module.finrank (ZMod 5) V := by
    rw [← h]
    norm_num
  simpa [V] using Nat.pow_right_injective (by norm_num : 2 ≤ 5) h2.symm

/-- Explicit rank-two basis of projective E[5]. -/
noncomputable def S2770_rankTwoBasis
    [CharZero K] [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] :
    (Fin 2 → ZMod 5) ≃ₗ[ZMod 5]
      AddSubgroup.torsionBy W.toProjective.Point ((5 : ℕ) : ℤ) :=
  by
    let V := AddSubgroup.torsionBy W.toProjective.Point ((5 : ℕ) : ℤ)
    have hcard : Nat.card V = 25 := by
      simpa [V] using S2769_projective_fiveTorsion_card W
    haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    haveI : Module.Finite (ZMod 5) V := Module.Finite.of_finite
    exact LinearEquiv.ofFinrankEq (R := ZMod 5) (Fin 2 → ZMod 5) V (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      simpa [V] using (S2770_finrank W).symm)

/-- Nonempty form of the rank-two basis. -/
theorem S2770_rankTwoBasis_nonempty :
    Nonempty ((Fin 2 → ZMod 5) ≃ₗ[ZMod 5]
      AddSubgroup.torsionBy W.toProjective.Point ((5 : ℕ) : ℤ)) :=
  ⟨S2770_rankTwoBasis W⟩

#check S2770_finrank
#check S2770_rankTwoBasis
#check S2770_rankTwoBasis_nonempty
#print axioms S2770_finrank
#print axioms S2770_rankTwoBasis_nonempty

end LeanFormal.IUT.XiFPaper.S2770RankTwoBasisActual
end
