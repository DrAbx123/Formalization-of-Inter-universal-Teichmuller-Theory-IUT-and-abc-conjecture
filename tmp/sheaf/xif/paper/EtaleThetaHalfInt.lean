import tmp.sheaf.xif.paper.TateJacobiHahnAttempt

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt

/-- Half-integer exponents, represented inside Q; all order/group instances are inherited. -/
abbrev HalfInt : Type := Rat

/-- The half-integer n / 2. -/
def halfInt (n : Int) : HalfInt := (n : Rat) / 2

/-- The [EtTh] theta exponent (1/2)*(n+1/2)^2 as a half-integer. -/
def thetaExponent (n : Int) : HalfInt :=
  ((n : Rat) + (1 / 2 : Rat)) ^ 2 / 2

/-- The [EtTh] theta U-exponent 2n+1. -/
def thetaUExponent (n : Int) : Int := 2 * n + 1

#check HalfInt
#check halfInt
#check thetaExponent
#check thetaUExponent
#check HahnSeries HalfInt
#check (fun (K : Type) [Field K] => HahnSeries HalfInt K)

example : AddCommGroup HalfInt := inferInstance
example : LinearOrder HalfInt := inferInstance
example : Zero HalfInt := inferInstance
example : IsOrderedCancelAddMonoid HalfInt := inferInstance


/-- The [EtTh] q-exponent after extracting the q^{-1/8} factor: n(n+1)/2. -/
def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

/-- Finite truncation of the [EtTh] theta series, with n ranging over [-N, N]. -/
noncomputable def etaleThetaTrunc (K : Type) [Field K] (N : Nat) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  Finset.sum (Finset.range (2 * N + 1)) (fun k : Nat =>
    let n : Int := (k : Int) - (N : Int)
    HahnSeries.single (thetaQExponent n)
      (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n)))

#check thetaQExponent
#check etaleThetaTrunc
end LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt
