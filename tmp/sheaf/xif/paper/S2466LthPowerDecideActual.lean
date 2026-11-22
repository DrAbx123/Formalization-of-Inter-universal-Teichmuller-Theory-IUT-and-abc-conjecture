import tmp.sheaf.xif.paper.S2129RootNecessaryActual
import tmp.sheaf.xif.paper.S2190RootSourceConditionsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2466LthPowerDecideActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2129RootNecessaryActual
open LeanFormal.IUT.XiFPaper.S2190RootSourceConditionsActual

universe u
variable {l : PrimeGeFive}
  (T : SourceNativeInitialThetaData.{0} l)
  (b : Bad (nativePlaceSelection T))

/-- If l does not divide the source ramification index, then q_v is not an
l-th power in Kv: every l-th power forces l ∣ eSource (S2190). -/
theorem S2466_not_lthPower_of_not_l_dvd_ramification
    (h : ¬ S2129LDivRamification T b) : ¬ S2190QLthPowerSource T b := by
  intro hroot
  exact h (l_dvd_ramification_of_lthPowerSource T b hroot)

/-- The necessary arithmetic condition for the l-th power target. -/
theorem S2466_lthPower_forces_l_dvd_ramification
    (h : S2190QLthPowerSource T b) : S2129LDivRamification T b :=
  l_dvd_ramification_of_lthPowerSource T b h

#print axioms S2466_not_lthPower_of_not_l_dvd_ramification
#print axioms S2466_lthPower_forces_l_dvd_ramification

end LeanFormal.IUT.XiFPaper.S2466LthPowerDecideActual
end