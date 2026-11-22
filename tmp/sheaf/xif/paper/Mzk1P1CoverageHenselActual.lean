/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.Geometry.TateWeierstrassPointEquation
import tmp.sheaf.xif.paper.Node09TateLaurentExpansionActual
import tmp.sheaf.xif.paper.Node09TateNewtonPolygonActual
import Mathlib.NumberTheory.Padics.Hensel
import LeanFormal.IUT.Foundations.Analysis.BanachFixedPointClosedBall
import Mathlib.Tactic

/-! # P1 §5.2: actual Laurent expansion and Hensel coverage gap -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P1CoverageHenselActual
open LeanFormal.IUT
open LeanFormal.IUT.TateCurve
open LeanFormal.IUT.XiFPaper.Node09TateLaurentExpansionActual

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The actual residual `X(u)-x`. -/
def coverageResidual (q x u : K) : K := tateWeierstrassX q u - x


/-- Actual Laurent expansion data: principal term plus positive/negative tails. -/
structure P1CoverageLaurentExpansionData (P : RigidTate.Parameter (K := K)) where
  principalPart : RigidTate.FundamentalDomain P → K
  tail : RigidTate.FundamentalDomain P → K
  expansion :
    ∀ u : RigidTate.FundamentalDomain P,
      tateWeierstrassX P.q u.1 = principalPart u + tail u

/-- The actual expansion is inhabited by the Node09 Laurent computation. -/
noncomputable def p1CoverageLaurentExpansionData
    (P : RigidTate.Parameter (K := K)) :
    P1CoverageLaurentExpansionData P where
  principalPart u := u.1 / (1 - u.1) ^ 2
  tail u := (∑' n : ℕ, RigidTate.xPositiveTerm P u (n + 1)) +
    RigidTate.xNegativeSeries P u
  expansion u := by
    simpa [add_assoc] using tateWeierstrassX_laurent_expansion P u

/-- Exact missing Hensel/Weierstrass-preparation root bridge: turn the Laurent
residual into an actual root `X(u)=x`.  No inhabitant. -/
structure P1CoverageHenselBridgeData (q x : K) where
  root : K
  root_spec : tateWeierstrassX q root = x

def P1CoverageHenselBridgeRequired (q x : K) : Prop :=
  Nonempty (P1CoverageHenselBridgeData q x)

theorem p1CoverageHenselBridgeRequired_iff_exists_root (q x : K) :
    P1CoverageHenselBridgeRequired q x ↔ ∃ u : K, tateWeierstrassX q u = x := by
  constructor
  · rintro ⟨D⟩; exact ⟨D.root, D.root_spec⟩
  · rintro ⟨u, hu⟩; exact ⟨⟨u, hu⟩⟩


/-- For `x` already in the image of `X`, the bridge is inhabited by the
actual point.  This is the honest partial construction; arbitrary `x` needs
the missing Hensel/Weierstrass root step. -/
def P1CoverageHenselBridgeData.ofPoint (q u : K) :
    P1CoverageHenselBridgeData q (tateWeierstrassX q u) :=
  ⟨u, rfl⟩

theorem P1CoverageHenselBridgeRequired_of_mem_range (q : K) {x : K}
    (hx : ∃ u : K, tateWeierstrassX q u = x) :
    P1CoverageHenselBridgeRequired q x :=
  p1CoverageHenselBridgeRequired_iff_exists_root q x |>.mpr hx


/- Mathlib's Hensel lemma is available, but only for a **polynomial** over a
ring `R` evaluated in `ℤ_[p]`.  `X(u)` is an infinite two-sided Laurent
series (principal term plus positive/negative tails), not a polynomial; the
tree contains no truncation-error / Laurent Newton-Hensel step converting a
polynomial root into an exact root of `X(u)=x`.  That is the exact bridge
gap, not absence of a Hensel donor. -/

end LeanFormal.IUT.XiFPaper.Mzk1P1CoverageHenselActual
