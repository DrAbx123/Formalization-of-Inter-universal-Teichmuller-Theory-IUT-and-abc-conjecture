import tmp.sheaf.xif.paper.S2768FiveTorsionCardActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ZMod

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2769RankTwoTorsionBasisActual

open WeierstrassCurve
open LeanFormal.IUT.XiFPaper.S2768FiveTorsionCardActual

/-- Projective/affine torsion equivalence for exponent 5. -/
noncomputable def S2769_torsionEquiv
    {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K) :
    AddSubgroup.torsionBy W.toProjective.Point ((5 : ℕ) : ℤ) ≃
      AddSubgroup.torsionBy W.toAffine.Point ((5 : ℕ) : ℤ) where
  toFun P :=
    ⟨(Projective.Point.toAffineAddEquiv W.toProjective) P.1, by
      have hP : ((5 : ℕ) : ℤ) • P.1 = 0 :=
        (AddSubgroup.torsionBy.nsmul_iff).mp P.2
      change (Projective.Point.toAffineAddEquiv W.toProjective) P.1 ∈
        AddSubgroup.torsionBy W.toAffine.Point ((5 : ℕ) : ℤ)
      rw [AddSubgroup.torsionBy.nsmul_iff]
      have hPnat : (5 : ℕ) • P.1 = 0 := by
        have h := (AddSubgroup.torsionBy.nsmul_iff).mp P.2
        simpa using h
      rw [← map_nsmul (Projective.Point.toAffineAddEquiv W.toProjective) 5 P.1, hPnat, map_zero]⟩
  invFun P :=
    ⟨(Projective.Point.toAffineAddEquiv W.toProjective).symm P.1, by
      have hP : ((5 : ℕ) : ℤ) • P.1 = 0 :=
        (AddSubgroup.torsionBy.nsmul_iff).mp P.2
      change (Projective.Point.toAffineAddEquiv W.toProjective).symm P.1 ∈
        AddSubgroup.torsionBy W.toProjective.Point ((5 : ℕ) : ℤ)
      rw [AddSubgroup.torsionBy.nsmul_iff]
      have hPnat : (5 : ℕ) • P.1 = 0 := by
        have h := (AddSubgroup.torsionBy.nsmul_iff).mp P.2
        simpa using h
      rw [← map_nsmul (Projective.Point.toAffineAddEquiv W.toProjective).symm 5 P.1, hPnat, map_zero]⟩
  left_inv P := by
    apply Subtype.ext
    exact (Projective.Point.toAffineAddEquiv W.toProjective).left_inv P.1
  right_inv P := by
    apply Subtype.ext
    exact (Projective.Point.toAffineAddEquiv W.toProjective).right_inv P.1

/-- Projective E[5] cardinality equals the affine S2768 cardinality. -/
theorem S2769_fiveTorsion_projective_card
    {K : Type*} [Field K] [CharZero K] [DecidableEq K] [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Nat.card (AddSubgroup.torsionBy W.toProjective.Point ((5 : ℕ) : ℤ)) = 25 := by
  rw [Nat.card_congr (S2769_torsionEquiv W)]
  simpa using S2768_fiveTorsion_card W

/-- The projective 5-torsion subgroup is a 2-dimensional ZMod-5 vector space. -/
theorem S2769_fiveTorsion_finrank
    {K : Type*} [Field K] [CharZero K] [DecidableEq K] [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Module.finrank (ZMod 5)
      (AddSubgroup.torsionBy W.toProjective.Point ((5 : ℕ) : ℤ)) = 2 := by
  change Module.finrank (ZMod 5)
    (AddSubgroup.torsionBy W.toProjective.Point ((5 : ℕ) : ℤ)) = 2
  let V := AddSubgroup.torsionBy W.toProjective.Point ((5 : ℕ) : ℤ)
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero (5 : ℕ) := ⟨by norm_num⟩
  have hcard : Nat.card V = 25 := S2769_fiveTorsion_projective_card W
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Module.Finite (ZMod 5) V := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod 5) (V := V)
  rw [hcard, Nat.card_zmod] at h
  have h25 : (5 : ℕ) ^ 2 = 5 ^ Module.finrank (ZMod 5) V := by
    rw [← h]
    norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 5) (by simpa [V] using h25.symm)

/-- Rank-two torsion basis: a ZMod-5 linear equivalence Fin 2 → ZMod 5 ≃ E[5]. -/
theorem S2769_rankTwoTorsionBasis
    {K : Type*} [Field K] [CharZero K] [DecidableEq K] [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Nonempty ((Fin 2 → ZMod 5) ≃ₗ[ZMod 5]
      AddSubgroup.torsionBy W.toProjective.Point ((5 : ℕ) : ℤ)) := by
  let V := AddSubgroup.torsionBy W.toProjective.Point ((5 : ℕ) : ℤ)
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero (5 : ℕ) := ⟨by norm_num⟩
  have hfr : Module.finrank (ZMod 5) V = 2 := by
    simpa [V] using S2769_fiveTorsion_finrank W
  haveI : Finite V := Nat.finite_of_card_ne_zero (by
    rw [S2769_fiveTorsion_projective_card W]; norm_num)
  haveI : Module.Finite (ZMod 5) V := Module.Finite.of_finite
  have hleft : Module.finrank (ZMod 5) (Fin 2 → ZMod 5) = 2 := by
    simp
  have h2 : Module.finrank (ZMod 5) (Fin 2 → ZMod 5) =
      Module.finrank (ZMod 5) V := by
    rw [hleft, hfr]
  exact (FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq).mpr h2

#check S2769_torsionEquiv
#check S2769_fiveTorsion_projective_card
#check S2769_fiveTorsion_finrank
#check S2769_rankTwoTorsionBasis
#print axioms S2769_fiveTorsion_finrank
#print axioms S2769_rankTwoTorsionBasis

end LeanFormal.IUT.XiFPaper.S2769RankTwoTorsionBasisActual
end
