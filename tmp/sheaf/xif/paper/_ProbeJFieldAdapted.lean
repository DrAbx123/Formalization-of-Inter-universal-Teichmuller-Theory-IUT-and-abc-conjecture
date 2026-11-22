import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveAnabelioid
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36

local instance s2773GaussianFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := by
  apply Fact.mk
  apply X_pow_sub_C_irreducible_of_prime (p := 2) Nat.prime_two
  intro b hb
  have hnonneg : 0 <= b ^ 2 := sq_nonneg b
  rw [hb] at hnonneg
  exact (not_le_of_gt (neg_lt_zero.mpr zero_lt_one)) hnonneg

example : (curveY2EqX3SubX.map (algebraMap ℚ GaussianField)).j = (1728 : GaussianField) := by
  rw [WeierstrassCurve.map_j]
  norm_num [curveY2EqX3SubX, WeierstrassCurve.j, WeierstrassCurve.c₄, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
