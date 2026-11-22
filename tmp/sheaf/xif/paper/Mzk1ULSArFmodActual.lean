/- SAr_tripodal 的 Fmod 层版本（Lead 裁 (a)）:
  SAr_tripodal_Fmod := logDifferentF Fmod + logConductorFActual T。
  附 calibration: logDifferentF F - logDifferentF Fmod = log|N(diff Fmod F)|/[F:Q]（tower 恒等）。
  donor: Mzk1HT82DiscrAssemblyActual.log_rootDiscr_eq_add（DONE）;
  Mzk1ULPaperLettersActual.logDifferentF/zero_le_logDifferentF（DONE）;
  Mzk1ULBadFPrimeSetActual.logConductorFActual/zero_le_logConductorFActual（DONE）。 -/
import tmp.sheaf.xif.paper.Mzk1HT82DiscrAssemblyActual
import tmp.sheaf.xif.paper.Mzk1ULPaperLettersActual
import tmp.sheaf.xif.paper.Mzk1ULBadFPrimeSetActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULSArFmodActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1ULBadFPrimeSetActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82DiscrAssemblyActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Fmod 层的 S_ar（paper L1572 的 dFtpd+fFtpd 口径，d_mod 归一）。 -/
noncomputable def SAr_tripodal_Fmod : ℝ :=
  logDifferentF T.arithmetic.Fmod + logConductorFActual (T := T)

/-- calibration 恒等: logDifferentF F - logDifferentF Fmod = log|N(diff Fmod F)|/[F:Q]。 -/
theorem logDifferentF_tower_eq :
    logDifferentF T.arithmetic.F =
      logDifferentF T.arithmetic.Fmod +
        Real.log ((Ideal.absNorm (differentIdeal (𝓞 T.arithmetic.Fmod) (𝓞 T.arithmetic.F)) : ℕ) : ℝ) /
          (Module.finrank ℚ T.arithmetic.F : ℝ) := by
  unfold logDifferentF
  exact log_rootDiscr_eq_add (K := T.arithmetic.Fmod) (L := T.arithmetic.F)

/-- calibration 项非负 ⇒ logDifferentF Fmod ≤ logDifferentF F。 -/
theorem logDifferentF_Fmod_le_F :
    logDifferentF T.arithmetic.Fmod ≤ logDifferentF T.arithmetic.F := by
  rw [logDifferentF_tower_eq T]
  have h1 : (0 : ℝ) ≤ Real.log ((Ideal.absNorm
      (differentIdeal (𝓞 T.arithmetic.Fmod) (𝓞 T.arithmetic.F)) : ℕ) : ℝ) /
      (Module.finrank ℚ T.arithmetic.F : ℝ) := by
    apply div_nonneg
    · apply Real.log_natCast_nonneg
    · positivity
  linarith

/-- SAr Fmod 非负（tripodal 版的基本性）。 -/
theorem zero_le_SAr_tripodal_Fmod : 0 ≤ SAr_tripodal_Fmod (T := T) := by
  unfold SAr_tripodal_Fmod
  exact add_nonneg (zero_le_logDifferentF T.arithmetic.Fmod) (zero_le_logConductorFActual (T := T))

#print axioms logDifferentF_tower_eq
#print axioms logDifferentF_Fmod_le_F
#print axioms zero_le_SAr_tripodal_Fmod

end LeanFormal.IUT.XiFPaper.Mzk1ULSArFmodActual
