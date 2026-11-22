import tmp.sheaf.xif.paper.S819PaperRootCompletionGeneratorActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S828PaperRootValueGroupActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S819PaperRootCompletionGeneratorActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

def PaperRootValueGroupDivisibility : Prop :=
  ∃ n : Int, ((qVFamily T b).order : Int) * (paperRamificationExponent T b : Int) =
    (2 * l.value : Int) * n

theorem paperRootInValueGroup_iff_divisibility :
    PaperRootInValueGroup (l := l) T b ↔
      PaperRootValueGroupDivisibility (l := l) T b := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have he : (paperRamificationExponent T b : Real) ≠ 0 := by
      exact_mod_cast ne_of_gt (LocalFieldLogarithm.logShellRamificationExponent_pos
        (K := CommonPrimeCompletion (qVFamTensorPlaces T b () ())) (p := qVFamTensorP T b))
    have h2l : (2 * (l.value : Real)) ≠ 0 := by
      exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
    have hreal : ((qVFamily T b).order : Real) *
        (paperRamificationExponent T b : Real) =
        (2 * (l.value : Real)) * (n : Real) := by
      have h := hn
      unfold paperCRoot at h
      rw [paperCRoot_eq_order_div] at h
      field_simp [he, h2l] at h
      linarith
    exact_mod_cast hreal
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    unfold paperCRoot
    rw [paperCRoot_eq_order_div]
    have hreal : ((qVFamily T b).order : Real) *
        (paperRamificationExponent T b : Real) =
        (2 * (l.value : Real)) * (n : Real) := by
      have := congrArg (fun z : Int => (z : Real)) hn
      push_cast at this
      exact this
    have he : (paperRamificationExponent T b : Real) ≠ 0 := by
      exact_mod_cast ne_of_gt (LocalFieldLogarithm.logShellRamificationExponent_pos
        (K := CommonPrimeCompletion (qVFamTensorPlaces T b () ())) (p := qVFamTensorP T b))
    have h2l : (2 * (l.value : Real)) ≠ 0 := by
      exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
    field_simp [he, h2l]
    linarith

theorem paperRootValueGroupNoGo_of_not_divisible
    (h : ¬ PaperRootValueGroupDivisibility (l := l) T b) :
    PaperRootValueGroupNoGo (l := l) T b :=
  fun hin => h ((paperRootInValueGroup_iff_divisibility (l := l) T b).mp hin)

end LeanFormal.IUT.XiFPaper.S828PaperRootValueGroupActualAdapted
end