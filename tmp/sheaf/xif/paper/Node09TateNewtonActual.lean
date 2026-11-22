import tmp.sheaf.xif.paper.Mzk1P1CoverageBridgeActual
import tmp.sheaf.xif.paper.Mzk1P1TailSumFinalActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09TateNewtonActual
open LeanFormal.IUT

variable {K : Type*} [Field K] [CharZero K]

/-- Principal residual X0(u)-x for X0(u)=u/(1-u)^2. -/
def principalResidual (x u : K) : K := u / (1 - u) ^ 2 - x

/-- Actual principal Newton map for the equation u/(1-u)^2=x. -/
def principalNewtonMap (x u : K) : K :=
  u - principalResidual x u * (1 - u) ^ 3 / (1 + u)

/-- Explicit principal root from s^2=4x+1: u=(s-1)/(s+1). -/
def principalRootFromSqrt (s : K) : K := (s - 1) / (s + 1)

/-- Actual Newton ball data (map, base point, radius) from an explicit root. -/
structure P1CoverageNewtonBallData where
  T : K → K
  x0 : K
  r : ℝ
  hr : 0 ≤ r

def principalNewtonBallData (x s : K) : P1CoverageNewtonBallData (K := K) where
  T := principalNewtonMap x
  x0 := principalRootFromSqrt s
  r := 0
  hr := le_refl 0

theorem principalNewtonMap_fixed (x u : K)
    (hx : x = u / (1 - u) ^ 2) :
    principalNewtonMap x u = u := by
  simp [principalNewtonMap, principalResidual, hx]


/-- Ball data with an explicit radius. -/
def principalNewtonBallDataWithRadius
    {K : Type*} [Field K] [CharZero K] (x s : K) (r : ℝ) (hr : 0 ≤ r) :
    P1CoverageNewtonBallData (K := K) where
  T := principalNewtonMap x
  x0 := principalRootFromSqrt s
  r := r
  hr := hr



/-- Inlined principal derivative norm (needed without the contraction donor olean). -/
theorem principal_derivative_norm_eq_one_inline {K : Type*} [NormedField K]
    (u : K) (hden : ‖1 - u‖ = 1) (hnum : ‖1 + u‖ = 1) :
    ‖(1 + u) / (1 - u) ^ 3‖ = 1 := by
  rw [norm_div, norm_pow, hden, hnum]
  norm_num



end LeanFormal.IUT.XiFPaper.Node09TateNewtonActual
end
