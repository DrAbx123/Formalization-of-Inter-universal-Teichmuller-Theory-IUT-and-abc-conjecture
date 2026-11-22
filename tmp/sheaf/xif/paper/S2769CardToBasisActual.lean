import tmp.sheaf.xif.paper.S2768FiveTorsionCardActual
import tmp.sheaf.xif.paper.S1725SourceTorsionFPrimeActual
import tmp.sheaf.xif.paper.S1906RankTwoTorsionActual
import tmp.sheaf.xif.paper.S1982D5FiveActual
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Free

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open WeierstrassCurve.Affine
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2769CardToBasisActual

local instance s2769S1906WElliptic : S1906W.IsElliptic := S1982W_isElliptic

/-- A finite ZMod-l vector space of cardinality l^2 has finrank 2. -/
theorem S2769_finrank_eq_two
    {l : Nat} [Fact (Nat.Prime l)]
    {M : Type*} [AddCommGroup M] [Module (ZMod l) M] [Finite M]
    (hcard : Nat.card M = l ^ 2) :
    Module.finrank (ZMod l) M = 2 := by
  haveI : Module.Finite (ZMod l) M := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod l) (V := M)
  rw [hcard, Nat.card_zmod] at h
  have h2 : 2 ≤ l := (Fact.out : Nat.Prime l).two_le
  exact (Nat.pow_right_injective h2 h).symm

/-- A rank-two torsion basis from the cardinality l^2. -/
noncomputable def S2769_basis_of_card
    {l : Nat} [Fact (Nat.Prime l)]
    {M : Type*} [AddCommGroup M] [Module (ZMod l) M] [Finite M]
    (hcard : Nat.card M = l ^ 2) :
    (Fin 2 → ZMod l) ≃ₗ[ZMod l] M :=
  LinearEquiv.ofFinrankEq (R := ZMod l) (Fin 2 → ZMod l) M (by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      S2769_finrank_eq_two hcard])

/-- The S1982 projective 5-torsion has finrank 2 over ZMod 5. -/
theorem S2769_S1982_finrank :
    Module.finrank (ZMod S1982Five.value) (S1720Curve.LTorsion S1982Five) = 2 := by
  haveI : Fact (Nat.Prime S1982Five.value) := ⟨S1982Five.prime⟩
  haveI : Finite (S1720Curve.LTorsion S1982Five) :=
    Nat.finite_of_card_ne_zero (by rw [S1982NatCard_LTorsion_five]; norm_num)
  have hcard : Nat.card (S1720Curve.LTorsion S1982Five) = S1982Five.value ^ 2 := by
    rw [S1982NatCard_LTorsion_five, S1982Five_value]; norm_num
  exact S2769_finrank_eq_two hcard

/-- An explicit rank-two basis of the S1982 projective 5-torsion, from the
cardinality and Module.finrank. -/
noncomputable def S2769_S1982Basis : S1725TorsionBasis S1982Five := by
  haveI : Fact (Nat.Prime S1982Five.value) := ⟨S1982Five.prime⟩
  haveI : Finite (S1720Curve.LTorsion S1982Five) :=
    Nat.finite_of_card_ne_zero (by rw [S1982NatCard_LTorsion_five]; norm_num)
  exact S2769_basis_of_card (l := S1982Five.value) (M := S1720Curve.LTorsion S1982Five)
    (by rw [S1982NatCard_LTorsion_five, S1982Five_value]; norm_num)

#check S2769_finrank_eq_two
#check S2769_basis_of_card
#check S2769_S1982_finrank
#check S2769_S1982Basis

end LeanFormal.IUT.XiFPaper.S2769CardToBasisActual
end