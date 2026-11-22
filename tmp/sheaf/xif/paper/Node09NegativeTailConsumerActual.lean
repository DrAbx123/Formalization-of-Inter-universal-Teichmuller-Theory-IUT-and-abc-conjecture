/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Node09TateNegativeTailLipschitzActual
import Mathlib.Tactic

/-! # Negative tail consumer (re-export of actual Node09 bounds) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09NegativeTailConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Node09TateNegativeTailLipschitzActual

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (P : RigidTate.Parameter (K := K))

theorem xNegativeTail_lipschitz_consumer
    (u v : RigidTate.FundamentalDomain P) :
    ‖(∑' n : ℕ, RigidTate.xNegativeTerm P v n) -
        (∑' n : ℕ, RigidTate.xNegativeTerm P u n)‖ ≤
      (‖P.q‖ / (1 - ‖P.q‖)) *
        (‖v.1 - u.1‖ / (‖u.1‖ * ‖v.1‖)) :=
  LeanFormal.IUT.XiFPaper.Node09TateNegativeTailLipschitzActual.xNegativeTail_lipschitz P u v

theorem xRemainder_lipschitz_consumer
    (u v : RigidTate.FundamentalDomain P) :
    ‖((∑' n : ℕ, RigidTate.xPositiveTerm P v (n + 1)) +
        RigidTate.xNegativeSeries P v) -
      ((∑' n : ℕ, RigidTate.xPositiveTerm P u (n + 1)) +
        RigidTate.xNegativeSeries P u)‖ ≤
      max (‖P.q‖ / (1 - ‖P.q‖))
          ((‖P.q‖ / (1 - ‖P.q‖)) / (‖u.1‖ * ‖v.1‖)) * ‖v.1 - u.1‖ :=
  LeanFormal.IUT.XiFPaper.Node09TateNegativeTailLipschitzActual.xRemainder_lipschitz P u v

end LeanFormal.IUT.XiFPaper.Node09NegativeTailConsumerActual
