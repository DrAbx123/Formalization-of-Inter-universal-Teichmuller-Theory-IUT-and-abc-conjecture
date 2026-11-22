import Mathlib.Tactic

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P1CoverageContractionActual

variable {K : Type*} [NormedField K]

/-- The principal derivative P'(u)=(1+u)/(1-u)^3 has norm one when both
1-u and 1+u have norm one (the fundamental-annulus case). -/
theorem principal_derivative_norm_eq_one (u : K)
    (hden : ‖1 - u‖ = 1) (hnum : ‖1 + u‖ = 1) :
    ‖(1 + u) / (1 - u) ^ 3‖ = 1 := by
  rw [norm_div, norm_pow, hden, hnum]
  norm_num

def Node09P1ContractionStatus : List String :=
  [ "actual: principal_derivative_norm_eq_one proves the principal derivative has norm one in the fundamental-annulus case",
    "actual support: Node09TateRemainderLipschitzActual.xPositiveTerm_dist_le and Node09TateTailLipschitzActual.xPositiveTail_lipschitz give termwise and summed positive-tail Lipschitz bounds",
    "MISSING hTcontract: a summed negative-half Lipschitz bound and the resulting contraction estimate for the Newton map; the bare Banach structure P1CoverageContractionData is only a specification, not an actual construction",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Mzk1P1CoverageContractionActual