import tmp.sheaf.xif.paper.Mzk1Prop58iImagesActual
import tmp.sheaf.xif.paper.Mzk1KummerThetaInterfaceActual
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier

/-!
# Mzk1LogShellConsumerChainActual — consumer theorems for the log-shell image layer
(P58IMG/IKT + tree SourceLogShellCarrier). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LogShellConsumerChainActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iImagesActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerThetaInterfaceActual

universe u

/-- Consumer: the unit layer is the log-image of all units (P58IMG). -/
theorem consumer_unitLayer_image (D : SourceLogShellDatum.{u}) :
    D.unitLayer = (fun u : D.Units => (D.logMap u).toAdd) '' (Set.univ : Set D.Units) :=
  unitLayer_eq_image_units D

/-- Consumer: the log-shell is the p*-inverse-scaled pre-log-shell (P58IMG). -/
theorem consumer_logShell_pStar (D : SourceLogShellDatum.{u}) :
    D.logShell = {a : D.K | (D.pStar : D.K) * a ∈ D.preLogShell} :=
  logShell_eq_pStar_invScaled_preLogShell D

/-- Consumer: the invariant image lies in the unit image (P58IMG). -/
theorem consumer_preLogShell_unitLayer (D : SourceLogShellDatum.{u}) :
    D.preLogShell ⊆ D.unitLayer :=
  preLogShell_subset_unitLayer D

/-- Consumer: the Kummer quotient is injective (IKT). -/
theorem consumer_kummer_quotient_injective {K : Type} [Field K] [CharZero K] {n : ℕ}
    [NeZero n] (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) :
    Function.Injective (AbsoluteKummerQuotient.absoluteKummerMapQuotient hμ) :=
  kummerQuotient_injective hμ

#check consumer_unitLayer_image
#check consumer_logShell_pStar
#check consumer_preLogShell_unitLayer
#check consumer_kummer_quotient_injective

end LeanFormal.IUT.XiFPaper.Mzk1LogShellConsumerChainActual
end
