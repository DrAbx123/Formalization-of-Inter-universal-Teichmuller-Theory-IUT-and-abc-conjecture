import tmp.sheaf.xif.paper.Mzk1XiEContainmentActual

/-! # Mzk1XiFConclusionActual — from genuine xi-e containment to the signed inequality

A531 assembly module: consumes the non-definitional xi-e containment of
Mzk1XiEContainmentActual and a log-volume map on the carrier, and derives the xi-f
signed comparison `logVol q <= thetaBound` under the (Theta-side) hypothesis that every
possible log-volume of the Theta-pilot representative is bounded by thetaBound.
Pure order-theoretic derivation; no new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1XiFConclusionActual

open CategoryTheory
open Iut.Multiradial
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentActual

universe u v w w'

variable {G : Type u} [Groupoid.{v} G] {A : Type w'} [Group A]
variable {R : RawOutput.{u, v, w} G A}

/-- xi-f conclusion from genuine containment: if the Theta-pilot's possible images all
have log-volume at most thetaBound, and the q-pilot lies in the possible images,
then the q-pilot log-volume is at most thetaBound. -/
theorem xi_f_signed_comparison {P : G} {X : Type*}
    (reg : R.F.obj P → Set X) (r : MRRep R P) (q : X)
    (logVol : X → Real) (thetaBound : Real)
    (hTheta : ∀ x, MRRep.mk (R := R) x = r → ∀ y ∈ reg x, logVol y <= thetaBound)
    (hContain : XiEContainment (R := R) reg r q) :
    logVol q <= thetaBound := by
  obtain ⟨x, hx, hq⟩ := exists_representative_of_containment reg r q hContain
  exact hTheta x hx q hq

/-- Signed Corollary 3.12 assembly: with qSigned = -logVol q and thetaSigned = -thetaBound,
the xi-f comparison gives the signed inequality `qSigned <= thetaSigned` (equivalently
`-|log q| <= -|log Theta|` in the calibrated convention). -/
theorem xi_f_signed_le {P : G} {X : Type*}
    (reg : R.F.obj P → Set X) (r : MRRep R P) (q : X)
    (logVol : X → Real) (thetaBound : Real)
    (hTheta : ∀ x, MRRep.mk (R := R) x = r → ∀ y ∈ reg x, logVol y <= thetaBound)
    (hContain : XiEContainment (R := R) reg r q) :
    -thetaBound <= -logVol q := by
  have h := xi_f_signed_comparison reg r q logVol thetaBound hTheta hContain
  linarith

/-- Consumer form with the possible-region bound: assume the bound on the whole possible
image set (the genuine Theta-side statement), then the q-pilot inequality follows from
the representative's containment. -/
theorem xi_f_signed_le_of_possibleRegion {P : G} {X : Type*}
    (reg : R.F.obj P → Set X) (x : R.F.obj P) (q : X)
    (logVol : X → Real) (thetaBound : Real)
    (hTheta : ∀ y ∈ MRRep.possibleRegion reg (MRRep.mk (R := R) x), logVol y <= thetaBound)
    (hq : q ∈ reg x) :
    -thetaBound <= -logVol q := by
  have hContain : XiEContainment (R := R) reg (MRRep.mk (R := R) x) q :=
    representative_subset_possibleRegion reg x hq
  have hle : logVol q <= thetaBound := hTheta q hContain
  linarith
#check xi_f_signed_comparison
#check xi_f_signed_le
#check xi_f_signed_le_of_possibleRegion

end LeanFormal.IUT.XiFPaper.Mzk1XiFConclusionActual
end
