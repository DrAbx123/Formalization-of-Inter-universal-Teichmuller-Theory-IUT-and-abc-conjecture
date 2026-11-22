import tmp.sheaf.xif.paper.S835PaperRootValueGroupIffActual
import tmp.sheaf.xif.paper.S795OrderSemanticsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S838QVFamilyDivisibilityActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S819PaperRootCompletionGeneratorActual
open LeanFormal.IUT.XiFPaper.S835PaperRootValueGroupIffActual
open LeanFormal.IUT.XiFPaper.S795OrderSemanticsActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem l_not_dvd_order :
    ¬ l.value ∣ (qVFamily T b).order := by
  intro h
  have hcop : Nat.Coprime (qVFamily T b).order l.value :=
    qVFamily_order_coprime_actual (l := l) T b
  have hcop' : Nat.Coprime l.value (qVFamily T b).order := hcop.symm
  have hone : l.value = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop' dvd_rfl h
  have h5 : 5 ≤ l.value := l.ge_five
  omega

theorem not_twoL_dvd_of_e_one
    (he : paperRamificationExponent T b = 1) :
    ¬ (2 * l.value ∣ paperRamificationExponent T b * (qVFamily T b).order) := by
  intro hd
  have hd' : 2 * l.value ∣ (qVFamily T b).order := by
    simpa [he] using hd
  have h2l : l.value ∣ 2 * l.value := by
    rw [mul_comm]
    exact dvd_mul_right l.value 2
  exact l_not_dvd_order T b (dvd_trans h2l hd')

theorem paperRootValueGroupNoGo_of_e_one
    (he : paperRamificationExponent T b = 1) :
    PaperRootValueGroupNoGo (l := l) T b := by
  have hnot : ¬ (2 * l.value ∣ paperRamificationExponent T b * (qVFamily T b).order) :=
    not_twoL_dvd_of_e_one T b he
  apply paperRootValueGroupNoGo_of_not_divisible (l := l) T b
  rintro ⟨n, hn⟩
  have hdiv : (2 * l.value : Int) ∣
      ((qVFamily T b).order : Int) * (paperRamificationExponent T b : Int) :=
    ⟨n, hn⟩
  have hnat : 2 * l.value ∣ paperRamificationExponent T b * (qVFamily T b).order := by
    have := hdiv
    -- cast divisibility to Nat divisibility
    exact_mod_cast (by simpa [mul_comm] using hdiv : (2 * l.value : Int) ∣
      (paperRamificationExponent T b : Int) * ((qVFamily T b).order : Int))
  exact hnot (by simpa [mul_comm] using hnat)

end LeanFormal.IUT.XiFPaper.S838QVFamilyDivisibilityActual
end