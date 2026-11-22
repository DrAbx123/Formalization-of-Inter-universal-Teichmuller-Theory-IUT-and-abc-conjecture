/--
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project, mainline lane (A490)
-/
import tmp.sheaf.lana.iut.Iut.Wall.NumericalWallHullActual
import tmp.sheaf.xif.paper.Mzk1LANAQPilotWallRegionActual

/-!
# NumericalWall: the q-pilot region reduction (A490)

Assembly of the numerical wall `Iut.Wall.NumericalWall D` from the hull lane
(`NumericalWallHullActual`: every log-volume below `-|log(Theta)|` is realized by an
adelic region in the hull of a single (Ind1)-image) and the q-pilot lane
(`Mzk1LANAQPilotWallRegionActual`: the constructed `{q_v O_v}` region has log-volume
`-|log(q)|`).

* `numericalWall_iff_rhs_ge_lhs` (new): the numerical wall is equivalent to the single
  real inequality `qPilot.lhs <= rhs` (i.e. `-|log(q)| <= -|log(Theta)|`); this is the
  `exists_adelic_iff` specialization at `x = qPilot.lhs`.
* `numericalWall_holds_of_rhs_ge_lhs` (new): the wall follows from that inequality.
* `numericalWall_holds_of_qPilotRegion_inHull` (new): the wall follows from the explicit
  named input that the constructed q-pilot region lies in the hull of a single
  (Ind1)-image.
* `numericalWallInput_iff`: the named input form of the remaining paper inequality.

No sorry/axiom/True placeholder; the remaining inequality is an explicit named
hypothesis, never a hidden axiom.
-/

namespace Iut

namespace Wall

universe u

variable (D : InitialThetaData.{0})

open LeanFormal.IUT.XiFPaper.Mzk1LANAQPilotWallRegionActual

/-- **New characterization of the numerical wall:** it is equivalent to the single real
  inequality `qPilot.lhs <= rhs` (the numerical content of the Corollary 3.12 variant).
  Proof: `hullActual_numericalWall_iff_exists_logVol` + `exists_adelic_iff` at
  `x = (concreteVariantData D).qPilot.lhs`. -/
theorem numericalWall_iff_rhs_ge_lhs :
    NumericalWall D ↔ (concreteVariantData D).qPilot.lhs ≤
      (concreteVariantData D).rhsData.rhs := by
  rw [hullActual_numericalWall_iff_exists_logVol]
  exact exists_adelic_iff D _

/-- The numerical wall from the explicit real inequality `-|log(q)| <= -|log(Theta)|`. -/
theorem numericalWall_holds_of_rhs_ge_lhs
    (h : (concreteVariantData D).qPilot.lhs ≤ (concreteVariantData D).rhsData.rhs) :
    NumericalWall D :=
  (numericalWall_iff_rhs_ge_lhs D).mpr h

/-- **Explicit named input form:** the (only) remaining paper inequality for the wall. -/
def NumericalWallInput : Prop :=
  (concreteVariantData D).qPilot.lhs ≤ (concreteVariantData D).rhsData.rhs

theorem numericalWallInput_iff : NumericalWallInput D ↔ NumericalWall D :=
  (numericalWall_iff_rhs_ge_lhs D).symm

/-- The wall from the explicit named input (no hidden axiom; the inequality is an
  argument of the theorem). -/
theorem numericalWall_holds_of_input (h : NumericalWallInput D) : NumericalWall D :=
  numericalWallInput_iff D |>.mpr h

/-- The wall from the q-pilot-region hull input: if the constructed `{q_v O_v}` region lies
  in the hull of a single (Ind1)-image, then `NumericalWall D` holds (its log-volume is
  `qPilot.lhs` by the q-pilot lane). -/
theorem numericalWall_holds_of_qPilotRegion_inHull
    (h : InHullOfImage D (qPilotWallRegion D)) : NumericalWall D :=
  (hullActual_numericalWall_iff_exists_logVol D).mpr
    ⟨qPilotWallRegion D, isAdelic_qPilotWallRegion D, h, by
      rw [logVol_qPilotWallRegion D, qPilot_lhs_eq_neg_scale D, neg_neg]⟩

/-- The q-pilot class form of the wall from the q-pilot lane (`Rss.mk` of the constructed
  region equals `symm (-qPilotScale)`), re-exported for downstream consumers. -/
theorem numericalWall_iff_rss_qPilotScale_reexport :
    NumericalWall D ↔ ∃ (U : Region D) (hU : IsAdelic D U),
      InHullOfImage D U ∧ Rss.mk D U hU = (rssEquiv D).symm (-qPilotScale D) :=
  numericalWall_iff_rss_qPilotScale D

/-- The named input is exactly the Corollary 3.12 variant for the concrete variant data
  (wall = restatement of the variant; `Checks.lean` `numericalWall_iff`). -/
theorem numericalWallInput_iff_variant :
    NumericalWallInput D ↔ Corollary312Variant (concreteVariantData D) :=
  (numericalWallInput_iff D).trans (numericalWall_iff D)

/-- Doc/audit note: the q-pilot-region hull hypothesis below is a SUFFICIENT explicit
  condition (it implies the named input); it is not claimed equivalent to it.  The exact
  named input is `NumericalWallInput` (`lhs <= rhs`, iff the wall by
  `numericalWallInput_iff`). -/
theorem qPilotRegionInHull_implies_input
    (h : InHullOfImage D (qPilotWallRegion D)) : NumericalWallInput D := by
  rw [numericalWallInput_iff]
  exact numericalWall_holds_of_qPilotRegion_inHull D h

end Wall

end Iut