import tmp.sheaf.xif.paper.S2240StrictConeIsoActual
import tmp.sheaf.xif.paper.S2123PresentationConeESActual
import tmp.sheaf.xif.paper.S1852CoherentCoverActual

/-! # S2276: presentation twist / strict-cone coherence for concrete PC/PB

For a strong target cover, the required coherent lift cone morphism and the
strict-cone comparison are already actual in S2240: `S2240ConeEssSurjAt` holds
for every strong target cover, hence `S2240ConeIsoAt`, the strict cone, and the
concrete S2130 two-pullback witness.  The uniform version over all recorded
(weak) covers is refuted by S2240NotCPresentationConeEssSurj.

This file packages those consequences; no new uniform construction is
fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2276PresentationTwistActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2130ExplicitD6Actual
open LeanFormal.IUT.XiFPaper.S2185ConcreteTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2240StrictConeIsoActual

universe u

/-- Strong target covers have the actual presentation coherence. -/
theorem S2276StrongCoverConeIso (Cs : StrongCover S1726Orbicurve)
    (B : S1728Cover) : S2240ConeIsoAt B (StrongCover.cover Cs) :=
  S2240ConeIsoAt_of_coneEssSurjAt B (StrongCover.cover Cs)
    (S2240ConeEssSurjAt_of_strongCover Cs B)

/-- The uniform weak-cover version is refuted. -/
theorem S2276UniformWeakRefuted : ¬ S2240FirstMissing :=
  S2240NotFirstMissing

#check S2276StrongCoverConeIso
#check S2276UniformWeakRefuted

end LeanFormal.IUT.XiFPaper.S2276PresentationTwistActual

end
