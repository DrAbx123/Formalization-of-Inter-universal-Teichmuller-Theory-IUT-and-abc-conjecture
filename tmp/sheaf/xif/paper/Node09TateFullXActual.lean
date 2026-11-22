import tmp.sheaf.xif.paper.Node09TateNewtonActual
import tmp.sheaf.xif.paper.Node09TateNegativeTailLipschitzActual
import LeanFormal.IUT.Foundations.Geometry.RigidTateSeries

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09TateFullXActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Node09TateNewtonActual

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

/-- Actual full-X remainder: positive tail plus negative half. -/
def xFullRemainder (P : RigidTate.Parameter (K := K))
    (u : RigidTate.FundamentalDomain P) : K :=
  (∑' n : ℕ, RigidTate.xPositiveTerm P u (n + 1)) + RigidTate.xNegativeSeries P u

/-- Actual full-X remainder Lipschitz (imported donor restated). -/
theorem xFullRemainder_lipschitz (P : RigidTate.Parameter (K := K))
    (u v : RigidTate.FundamentalDomain P) :
    ‖xFullRemainder P v - xFullRemainder P u‖ ≤
      max (‖P.q‖ / (1 - ‖P.q‖))
          ((‖P.q‖ / (1 - ‖P.q‖)) / (‖u.1‖ * ‖v.1‖)) * ‖v.1 - u.1‖ :=
  Node09TateNegativeTailLipschitzActual.xRemainder_lipschitz P u v

/-- Actual full-X Newton map for X(q,·)=x. -/
def fullXNewtonMap (P : RigidTate.Parameter (K := K)) (x u : K) : K :=
  u - (TateCurve.tateWeierstrassX P.q u - x) * (1 - u) ^ 3 / (1 + u)

/-- The full-X Newton map fixes any exact point of X(q,·); zero residual makes
the singular 1+u irrelevant via zero_div. -/
theorem fullXNewtonMap_fixed (P : RigidTate.Parameter (K := K)) (x u : K)
    (hx : x = TateCurve.tateWeierstrassX P.q u) :
    fullXNewtonMap P x u = u := by
  simp [fullXNewtonMap, hx]

/-- Actual singleton MapsTo for the full-X Newton map. -/
theorem fullXNewtonMap_mapsTo_singleton (P : RigidTate.Parameter (K := K)) (x u : K)
    (hx : x = TateCurve.tateWeierstrassX P.q u) :
    Set.MapsTo (fullXNewtonMap P x) ({u} : Set K) ({u} : Set K) := by
  intro y hy
  rw [Set.mem_singleton_iff] at hy ⊢
  subst y
  exact fullXNewtonMap_fixed P x u hx

/-- Actual r=0 ball data for the full-X Newton map. -/
def fullXNewtonBallData (P : RigidTate.Parameter (K := K)) (x u : K) :
    P1CoverageNewtonBallData (K := K) where
  T := fullXNewtonMap P x
  x0 := u
  r := 0
  hr := le_refl 0

end LeanFormal.IUT.XiFPaper.Node09TateFullXActual
end
