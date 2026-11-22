/- hbad local scaffold (paper L1555-1572 / Prop1.3(i)) - conditional interface, NOT closure.
   Structure LocalProp13Data: per-vQ localLogS/D/F + per-place bound + sum identifications;
   theorem global_of_local derives log sQ <= 2*d_mod*SAr_Ftpd from it (real implication). -/
import tmp.sheaf.xif.paper.Mzk1ULHSQLambdaNumericTruncActual
import tmp.sheaf.xif.paper.Mzk1ULSArFtpdIdentityActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadLocalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHSQLambdaNumericTruncActual
open LeanFormal.IUT.XiFPaper.Mzk1ULSArFtpdIdentityActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Per-vQ local Prop1.3(i) data (scaffolding): local log s/d/f with per-place bound and sum identifications. -/
structure LocalProp13Data (lam : ℂ) (hlam : IsAlgebraic ℚ lam)
    (hE : (legendreWeierstrassCurve lam).IsElliptic)
    (VBad : Set (FinitePlace (Iut.fieldOfModuli ℂ (legendreWeierstrassCurve lam)))) where
  localLogS : ℝ
  localLogD : ℝ
  localLogF : ℝ
  local_bound : localLogS ≤ 2 * (localLogD + localLogF)
  global_s_le : Real.log (sQPaper T) ≤ localLogS
  sum_d : (Module.finrank ℚ (T.arithmetic.Fmod) : ℝ) *
    (letI := numberField_FtpdLam lam hlam
     logDifferentF (FtpdLam lam)) ≤ localLogD
  sum_f : (Module.finrank ℚ (T.arithmetic.Fmod) : ℝ) *
    logConductorDegOf ℂ (legendreWeierstrassCurve lam) VBad ≤ localLogF

/-- From LocalProp13Data derive the global bound log sQ <= 2*d_mod*SAr_Ftpd. -/
theorem global_of_local (lam : ℂ) (hlam : IsAlgebraic ℚ lam)
    (hE : (legendreWeierstrassCurve lam).IsElliptic)
    (VBad : Set (FinitePlace (Iut.fieldOfModuli ℂ (legendreWeierstrassCurve lam))))
    (D : LocalProp13Data (T := T) lam hlam hE VBad) :
    Real.log (sQPaper T) ≤
      2 * (Module.finrank ℚ (T.arithmetic.Fmod) : ℝ) *
        SAr_tripodal_Ftpd lam hlam hE VBad := by
  have h1 : Real.log (sQPaper T) ≤ 2 * (D.localLogD + D.localLogF) := by
    have hb := D.local_bound
    linarith [D.global_s_le]
  have h2 : (Module.finrank ℚ (T.arithmetic.Fmod) : ℝ) *
      (letI := numberField_FtpdLam lam hlam
       logDifferentF (FtpdLam lam)) +
      (Module.finrank ℚ (T.arithmetic.Fmod) : ℝ) *
        logConductorDegOf ℂ (legendreWeierstrassCurve lam) VBad ≤
      D.localLogD + D.localLogF := by
    linarith [D.sum_d, D.sum_f]
  have h3 : (Module.finrank ℚ (T.arithmetic.Fmod) : ℝ) *
      SAr_tripodal_Ftpd lam hlam hE VBad =
      (Module.finrank ℚ (T.arithmetic.Fmod) : ℝ) *
        (letI := numberField_FtpdLam lam hlam
         logDifferentF (FtpdLam lam)) +
      (Module.finrank ℚ (T.arithmetic.Fmod) : ℝ) *
        logConductorDegOf ℂ (legendreWeierstrassCurve lam) VBad := by
    unfold SAr_tripodal_Ftpd
    ring
  linarith [h1, h2, h3]

#print axioms global_of_local

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadLocalActual
