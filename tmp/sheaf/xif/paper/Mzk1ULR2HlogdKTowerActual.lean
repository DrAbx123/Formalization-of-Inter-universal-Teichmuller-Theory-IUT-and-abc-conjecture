/- R2 (route 4.4): hlogdK actual tower 到 SAr_F + 2 log l + 21。
   donors: Mzk1G1HlogKAssemblyActual.hlogK_of_relative_different_bound (DONE 23:08:51):
     log dK <= log dF + logConductorFActual + 2 log l  (relative different bound as input);
           Mzk1G1F7DifferentExponentBoundsActual good/wild donors (differentExponent_*);
           Mzk1ULHbadFLevelActual.SAr_F := logDifferentF F + logConductorFActual (DONE 14:47:18);
           paper IV L1414-1425: log dF + log fF <= log dFtpd + log fFtpd + 21 (F vs Ftpd, PROVEN in paper).
   本件给 tower-shape 结论: logDifferentK <= SAr_F + 2 log l + 21（21 为 paper 明文 slack, 不吸收 h 槽 [F:Q]）。 -/
import tmp.sheaf.xif.paper.Mzk1G1HlogKAssemblyActual
import tmp.sheaf.xif.paper.Mzk1ULHbadFLevelActual
import tmp.sheaf.xif.paper.Mzk1G1F7DifferentExponentBoundsActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR2HlogdKTowerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1G1HlogKAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHbadFLevelActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- R2 hlogdK tower: relative different 上界 ⇒ logDifferentK <= SAr_F + 2log l + 21。 -/
theorem hlogdK_tower (hbound : Real.log
    ((Ideal.absNorm (differentIdeal (𝓞 T.arithmetic.F) (𝓞 T.arithmetic.K)) : Nat) : Real) ≤
      (Module.finrank ℚ T.arithmetic.K : Real) *
        (LeanFormal.IUT.XiFPaper.Mzk1ULBadFPrimeSetActual.logConductorFActual T +
          2 * Real.log (l.value : Real))) :
    Real.log (NumberField.rootDiscr T.arithmetic.K) ≤
      SAr_F (T := T) + 2 * Real.log (l.value : Real) + 21 := by
  have h := Mzk1G1HlogKAssemblyActual.hlogK_of_relative_different_bound (T := T) hbound
  unfold SAr_F logDifferentF
  linarith

#print axioms hlogdK_tower

end LeanFormal.IUT.XiFPaper.Mzk1ULR2HlogdKTowerActual