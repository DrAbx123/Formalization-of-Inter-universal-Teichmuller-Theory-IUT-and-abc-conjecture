/- G1a Fermat finite degree from chart rank. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatChartSchemeActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartSchemeActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatFiniteDegreeActual
def fermatFiniteDegree (n : Nat) : Nat := n
theorem fermat_chart_finite_degree (n : Nat) (hn : 0 < n) :
    Module.finrank (Polynomial ℚ) (fermatU0Ring n) = fermatFiniteDegree n :=
  fermatU0Ring_finrank n hn
#print axioms fermat_chart_finite_degree
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatFiniteDegreeActual
