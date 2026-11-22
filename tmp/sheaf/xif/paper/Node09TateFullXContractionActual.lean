import tmp.sheaf.xif.paper.Node09TateNegativeTailLipschitzActual
import tmp.sheaf.xif.paper.Node09TateLaurentExpansionActual

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.Node09TateFullXContractionActual

universe u
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

open RigidTate in
theorem fullX_sub_principal_lipschitz
    (P : RigidTate.Parameter (K := K))
    (u v : RigidTate.FundamentalDomain P) :
    ‖(TateCurve.tateWeierstrassX P.q v.1 - v.1 / (1 - v.1) ^ 2) -
      (TateCurve.tateWeierstrassX P.q u.1 - u.1 / (1 - u.1) ^ 2)‖ ≤
      max (‖P.q‖ / (1 - ‖P.q‖))
          ((‖P.q‖ / (1 - ‖P.q‖)) / (‖u.1‖ * ‖v.1‖)) * ‖v.1 - u.1‖ := by
  have htail : ∀ w : RigidTate.FundamentalDomain P,
      TateCurve.tateWeierstrassX P.q w.1 - w.1 / (1 - w.1) ^ 2 =
        (∑' n : ℕ, RigidTate.xPositiveTerm P w (n + 1)) +
          RigidTate.xNegativeSeries P w := by
    intro w
    rw [Node09TateLaurentExpansionActual.tateWeierstrassX_laurent_expansion P w]
    ring
  rw [htail v, htail u]
  exact Node09TateNegativeTailLipschitzActual.xRemainder_lipschitz P u v

def Node09TateFullXContractionStatus : List String :=
  [ "actual: fullX_sub_principal_lipschitz shows the full X minus principal part has exactly the tail difference, and its Lipschitz bound is xRemainder_lipschitz",
    "BLOCKER: a singleton fixed point for full X cannot use the principal root; X(root)-x = tail(root) generally nonzero, so hTmaps for full X needs an actual full root X(u)=x (Hensel/coverage)",
    "BLOCKER: the Banach/Newton contraction for full X needs a uniform c<1 on a ball; the tail Lipschitz constant depends on u,v and blows up as u or v approaches 0; a uniform bound requires an annulus restriction not present in the source",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09TateFullXContractionActual