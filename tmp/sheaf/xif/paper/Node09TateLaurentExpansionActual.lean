import LeanFormal.IUT.Foundations.Geometry.RigidTateSeriesTwoSidedSplit
import LeanFormal.IUT.Foundations.Geometry.TateWeierstrassPointEquation

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.Node09TateLaurentExpansionActual

universe u

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem tateWeierstrassX_twoSided
    (P : RigidTate.Parameter (K := K)) (u : RigidTate.FundamentalDomain P) :
    TateCurve.tateWeierstrassX P.q u.1 =
      RigidTate.xPositiveSeries P u + RigidTate.xNegativeSeries P u := by
  rw [TateCurve.tateWeierstrassX,
    RigidTate.coordinateSeries_eq_xPositiveSeries_add_xNegativeSeries P u]

theorem xPositiveTerm_zero_eq
    (P : RigidTate.Parameter (K := K)) (u : RigidTate.FundamentalDomain P) :
    RigidTate.xPositiveTerm P u 0 = u.1 / (1 - u.1) ^ 2 := by
  simp [RigidTate.xPositiveTerm, RigidTate.positiveArgument]

theorem tateWeierstrassX_laurent_expansion
    (P : RigidTate.Parameter (K := K)) (u : RigidTate.FundamentalDomain P) :
    TateCurve.tateWeierstrassX P.q u.1 =
      u.1 / (1 - u.1) ^ 2 +
        (∑' n : ℕ, RigidTate.xPositiveTerm P u (n + 1)) +
        RigidTate.xNegativeSeries P u := by
  rw [tateWeierstrassX_twoSided P u, RigidTate.xPositiveSeries,
    (RigidTate.Term.xPositiveTerm_summable P u).tsum_eq_zero_add,
    xPositiveTerm_zero_eq P u, add_assoc]

theorem xPositiveTerm_zero_norm
    (P : RigidTate.Parameter (K := K)) (u : RigidTate.FundamentalDomain P) :
    ‖RigidTate.xPositiveTerm P u 0‖ = ‖u.1‖ / ‖1 - u.1‖ ^ 2 := by
  rw [xPositiveTerm_zero_eq, norm_div, norm_pow]

def Node09TateLaurentExpansionStatus : List String :=
  [ "actual: tateWeierstrassX is the sum of the two one-sided Laurent halves on the rigid fundamental annulus",
    "actual: principal term u/(1-u)^2 extracted via tsum_eq_zero_add; norm = ||u||/||1-u||^2, pole order exactly 2 at u=1",
    "remaining for orbit separation: zero-count/Newton-polygon for X(u)=x using xPositiveTerm_norm_le / xNegativeTerm_norm, plus Y inversion branch selection",
    "remaining for coverage: Weierstrass preparation/Hensel; not present",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09TateLaurentExpansionActual