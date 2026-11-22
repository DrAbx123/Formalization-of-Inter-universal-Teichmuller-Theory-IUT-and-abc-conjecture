import tmp.sheaf.xif.paper.S1864GeneralPullbackStackActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1832ActualCoverPullbacksActual
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1762CoverLimitsActual

/-- The consumer check: the S1864 obligation, instantiated at any cospan, yields
the S1832 categorical pullback obligation. -/
theorem S1864Consumer_check (h : S1864FirstMissingPseudopullbackStack) :
    S1832FirstMissingPullback :=
  S1864FirstMissing_to_S1832 h

/-- The consumer check: the obligation form gives the named stack statement. -/
theorem S1864Consumer_stack (h : S1864FirstMissingPseudopullbackStack) :
    S1864FirstMissingIsoCommaStack :=
  S1864FirstMissing_to_isoCommaStack h

/-- The consumer check: the obligation gives S1762's finite-limit field. -/
theorem S1864Consumer_limits (h : S1864FirstMissingPseudopullbackStack) :
    LeanFormal.IUT.XiFPaper.S1736CoverGaloisCategoryActual.S1736ObligationFiniteLimits
      (F := S1762K) (X := S1762X) :=
  S1864HasFiniteLimitsActual h

end
