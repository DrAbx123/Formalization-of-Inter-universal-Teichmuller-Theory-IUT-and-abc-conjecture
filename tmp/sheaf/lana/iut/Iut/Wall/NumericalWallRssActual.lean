import tmp.sheaf.lana.iut.Iut.Wall.Checks
import tmp.sheaf.lana.iut.Iut.Wall.QPilotRegion

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# NumericalWallRssActual — the R_ss side of the numerical wall

Equality chain on the `rssEquiv`/`qPilot.lhs` side: any adelic region whose
log-volume is `qPilot.lhs` has `Rss.mk` equal to the inverse image of that real
number under `rssEquiv`.  Specialized to `qRegion`, and to an `archScale` dilate
whose log-volume is adjusted to `qPilot.lhs`; then the selected region yields
`NumericalWall D` through `numericalWall_iff_rss`.  No sorry/axiom. -/

namespace Iut

namespace Wall

variable (D : InitialThetaData.{0})

/-- Core `R_ss` equality: a region of log-volume `qPilot.lhs` represents the
corresponding real point. -/
theorem rss_mk_eq_symm_qPilotLhs_of_logVol (U : Region D) (hU : IsAdelic D U)
    (hlog : logVol D U = (concreteVariantData D).qPilot.lhs) :
    Rss.mk D U hU = (rssEquiv D).symm ((concreteVariantData D).qPilot.lhs) := by
  apply (rssEquiv D).injective
  rw [Equiv.apply_symm_apply]
  change Rss.logVol D (Rss.mk D U hU) = (concreteVariantData D).qPilot.lhs
  rw [Rss.logVol_mk, hlog]

/-- The constructed `qRegion` represents `qPilot.lhs` in `R_ss`. -/
theorem rss_mk_qRegion_eq_symm_qPilotLhs :
    Rss.mk D (qRegion D) (isAdelic_qRegion D) =
      (rssEquiv D).symm ((concreteVariantData D).qPilot.lhs) :=
  rss_mk_eq_symm_qPilotLhs_of_logVol D (qRegion D) (isAdelic_qRegion D)
    (logVol_qRegion D)

/-- An `archScale` dilate with log-volume tuned to `qPilot.lhs` represents the
same `R_ss` point. -/
theorem rss_mk_archScale_eq_symm_qPilotLhs_of_logVol (U : Region D) (hU : IsAdelic D U)
    (t : ℝ) (ht : 0 < t)
    (hlog : logVol D U + Real.log t = (concreteVariantData D).qPilot.lhs) :
    Rss.mk D (archScale D t U) (isAdelic_archScale D ht hU) =
      (rssEquiv D).symm ((concreteVariantData D).qPilot.lhs) := by
  refine rss_mk_eq_symm_qPilotLhs_of_logVol D _ _ ?_
  rw [logVol_archScale D ht hU]
  exact hlog

/-- A selected adelic hull region with log-volume `qPilot.lhs` gives
`NumericalWall D` through the proved `numericalWall_iff_rss`. -/
theorem numericalWall_of_adelicHull_logVol (U : Region D) (hU : IsAdelic D U)
    (hI : InHullOfImage D U)
    (hlog : logVol D U = (concreteVariantData D).qPilot.lhs) :
    NumericalWall D :=
  (numericalWall_iff_rss D).mpr
    ⟨U, hU, hI, rss_mk_eq_symm_qPilotLhs_of_logVol D U hU hlog⟩

end Wall

end Iut
