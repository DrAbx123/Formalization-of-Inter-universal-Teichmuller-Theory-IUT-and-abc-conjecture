import tmp.sheaf.xif.paper.LogThetaLatticeActual
import tmp.sheaf.xif.paper.ThetaLinkPositionConnectionActual

/-!
# Actual compatibility of the Theta-link position with the log-theta-lattice

This file proves the actual horizontal/vertical compatibility of the Theta-link
comparison object with the log-theta-lattice:

* the comparison link is the lattice horizontal link (rfl);
* horizontal-then-vertical equals vertical-then-horizontal for every (n,m),
  proved by actual family transitivity I.linkAt_trans;
* the (0,0) Theta-link position is the (0,0) horizontal comparison, and its
  square with the vertical link commutes.

No missing data, no arbitrary link, no inequality.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ThetaLinkLatticeCompatibilityActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.LogThetaLatticeActual
open LeanFormal.IUT.XiFPaper.ThetaLinkPositionConnectionActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual comparison at (n,m) is the lattice horizontal link. -/
theorem comparison_link_eq_horizontal (n m : Int) :
    (ActualThetaLinkComparison.at (I := I) n m).link =
      (ActualLogThetaLattice.actual (I := I)).horizontal n m := rfl

/-- The actual horizontal-then-vertical square commutes. -/
theorem comparison_square_commutes (n m : Int) :
    HodgeTheaterLink.trans
        (ActualThetaLinkComparison.at (I := I) n m).link
        ((ActualLogThetaLattice.actual (I := I)).vertical (n + 1) m) =
      HodgeTheaterLink.trans
        ((ActualLogThetaLattice.actual (I := I)).vertical n m)
        (ActualThetaLinkComparison.at (I := I) n (m + 1)).link := by
  rw [ActualThetaLinkComparison.at_link,
    ActualLogThetaLattice.actual_vertical,
    ActualLogThetaLattice.actual_vertical,
    ActualThetaLinkComparison.at_link]
  rw [I.linkAt_trans n m (n + 1) m (n + 1) (m + 1)]
  rw [I.linkAt_trans n m n (m + 1) (n + 1) (m + 1)]
  rfl

/-- The actual (0,0) position link is the (0,0) comparison link. -/
theorem position_link_eq_comparison_link :
    (actualThetaLinkPosition (I := I)).link =
      (actualThetaLinkComparison (I := I)).link := rfl

/-- The actual (0,0) position link is the (0,0) lattice horizontal link. -/
theorem position_link_eq_lattice_horizontal :
    (actualThetaLinkPosition (I := I)).link =
      (ActualLogThetaLattice.actual (I := I)).horizontal 0 0 := rfl

/-- The actual position square commutes at (0,0). -/
theorem position_square_commutes :
    HodgeTheaterLink.trans
        (actualThetaLinkPosition (I := I)).link
        ((ActualLogThetaLattice.actual (I := I)).vertical 1 0) =
      HodgeTheaterLink.trans
        ((ActualLogThetaLattice.actual (I := I)).vertical 0 0)
        (ActualThetaLinkComparison.at (I := I) 0 1).link := by
  simpa only [position_link_eq_comparison_link] using
    comparison_square_commutes (I := I) 0 0

/-- The actual position square output is the common link to (1,1). -/
theorem position_square_output :
    HodgeTheaterLink.trans
        (actualThetaLinkPosition (I := I)).link
        ((ActualLogThetaLattice.actual (I := I)).vertical 1 0) =
      I.linkAt 0 0 1 1 := by
  rw [ActualThetaLinkPosition_link (I := I),
    ActualLogThetaLattice.actual_vertical]
  exact I.linkAt_trans 0 0 1 0 1 1

/-- The actual comparison square output is the same common link to (1,1). -/
theorem comparison_square_output :
    HodgeTheaterLink.trans
        (ActualThetaLinkComparison.at (I := I) 0 0).link
        ((ActualLogThetaLattice.actual (I := I)).vertical 1 0) =
      I.linkAt 0 0 1 1 := by
  rw [ActualThetaLinkComparison.at_link,
    ActualLogThetaLattice.actual_vertical]
  exact I.linkAt_trans 0 0 1 0 1 1

/-- The actual horizontal/vertical projection of the (0,0) comparison. -/
theorem comparison_horizontal_projection :
    (ActualThetaLinkComparison.at (I := I) 0 0).stripIso =
      (I.linkAt 0 0 1 0).primeStripEquiv := rfl

end LeanFormal.IUT.XiFPaper.ThetaLinkLatticeCompatibilityActual

end
