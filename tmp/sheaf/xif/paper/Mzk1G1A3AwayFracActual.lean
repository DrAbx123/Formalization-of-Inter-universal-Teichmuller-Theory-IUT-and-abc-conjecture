/- A3 / F2.3: `Away f` of the Fermat chart ring has the same fraction ring.

  STATUS: the mathematical content is proved **conditional on the `Algebra`/`IsScalarTower`
  instances relating `Localization.Away f` to `FractionRing (R n)`**, whose construction is the
  remaining obligation (see coord/EXPLICIT-PARAM-AUDIT-GRACE.md §F2.3): Mathlib does not
  provide `Algebra (Localization.Away f) (FractionRing (R n))` automatically, and the manual
  construction via `IsLocalization.lift` hits the following issues (recorded for the next
  batch): (i) `IsLocalization.map_units` argument shape for `nonZeroDivisors`; (ii) the
  `IsUnit (algebraMap (R n) (FractionRing (R n)) (f^k))` vs `(algebraMap f)^k` rewriting;
  (iii) the compatible `IsScalarTower` (the `algebraMap` of the lifted map must be checked
  against `IsLocalization.lift_comp`).

  What IS unconditional here: `Mzk1G1A3ChartFracActual.chartRing_isDomain` (11:23:32), i.e.
  `IsDomain (R n)`, the prerequisite of the bridge. No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1A3ChartFracActual
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1A3ChartFracActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual

variable (n : Nat)

/-- **`Away f` 的分数环桥（条件形式）**：给定 `Algebra`/`IsScalarTower` 实例（构造为待消义务），
    `Away f` 的分数环就是 `FractionRing (R n)`。 -/
theorem away_isFractionRing_of_algebra (hn : 0 < n) (f : R n) (hf : f ≠ 0)
    [Algebra (Localization.Away f) (FractionRing (R n))]
    [IsScalarTower (R n) (Localization.Away f) (FractionRing (R n))] :
    IsFractionRing (Localization.Away f) (FractionRing (R n)) := by
  haveI : IsDomain (R n) := chartRing_isDomain n hn
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (M := Submonoid.powers f) (R := R n) (Localization.Away f) (FractionRing (R n))

#print axioms away_isFractionRing_of_algebra

end LeanFormal.IUT.XiFPaper.Mzk1G1A3ChartFracActual
