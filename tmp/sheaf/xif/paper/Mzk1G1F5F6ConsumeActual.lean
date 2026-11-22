import tmp.sheaf.xif.paper.Mzk1G1F6EtaChoiceActual
import tmp.sheaf.xif.paper.Mzk1HT84F4F5InterfaceActual
import Mathlib.Tactic
/-!
# F5/F6 consumption

Route F5 (H-T §8.4): `(1-ηκ)h_ω ≤ (1+η)D(L)+C` (`Mzk1HT84F4F5InterfaceActual.F5Statement`,
NO INHABITANT).  Route F6 (§8.4 L800-808): `h_ω ≤ (1+δ)D + C_{n,δ}`.
`Mzk1G1F6EtaChoiceActual.routeF6_of_F1_to_F5_choice` already eliminates the η arithmetic
hypotheses; this file records the consumer shape used by the P8 assembly.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.F5F6ConsumeActual
open LeanFormal.IUT.XiFPaper.Mzk1HT86F6InterfaceActual
open LeanFormal.IUT.XiFPaper.F6EtaChoiceActual

/-- F5 + actual F5 data + `0≤κmax`, `0≤C5` ⇒ F6 with constant `max C6 (2C5)`. -/
theorem f6_eta_choice_consumption (D : RouteHTData) (deg : ℝ)
    (h5 : RouteF5Statement D) (hκ0 : 0 ≤ D.κmax) (hC5 : 0 ≤ D.C5) :
    RouteF6StatementWith D deg (max D.C6 (2 * D.C5)) :=
  routeF6_of_F1_to_F5_choice D deg h5 hκ0 hC5

#print axioms f6_eta_choice_consumption
end LeanFormal.IUT.XiFPaper.F5F6ConsumeActual
end