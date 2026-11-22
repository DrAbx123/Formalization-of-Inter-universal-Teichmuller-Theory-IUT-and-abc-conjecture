import tmp.sheaf.xif.paper.S3129IQHullLogVolumeSourceActual
import tmp.sheaf.xif.paper.S3132ConcreteSourceNormalizationClosureActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3132ConcreteSourceNormalizationClosureActual

namespace LeanFormal.IUT.XiFPaper.AbsTopIII03Cor510Actual

/-!
# STEP 0 prior-art: Cor 5.10|Local Volumes|integralLogShell|HaarTranslateRealLineLogCompatibility -> hits LeanFormal/IUT/IUTIII/.../HaarTranslateRealLineLogCompatibility.lean:6, SourceLogShellActionCompatibility.lean:52, S3129IQHullLogVolumeSourceActual:151 -> REUSE (no re-proof).

# [AbsTopIII] 03: Cor 5.10 (concrete, C) - finite log-volume of the log-shell

Corpus: papers/motizuki_corpus/text/Topics in Absolute Anabelian Geometry III.txt
lines 8587-8610: Cor 5.10 (i) Finite Log-volume (the log-shell is of finite
log-volume; p_v-adic reading), (ii) Log-Frobenius Compatibility of Log-volumes,
(iii) Panalocalization, (iv) Mono-analyticization.  The concrete p-adic side we
can prove here is the FINITE LOG-VOLUME statement for the actual source log-shell:
its actual Haar mass is 1 (S3129:151), hence finite and positive, and its
log-volume is 0 (normalization, Prop 5.7(i)(a)).  (ii)/(iv) are recorded as
dictionary statements; the p_v-adic scaling law is the named remaining object
(no claim).
-/

/-- Concrete volume of a set: actual source Haar measure, real-valued. -/
noncomputable def cor510Volume (A : Set concreteLogShellField) : ℝ :=
  (sourceHullHaar A).toReal

/-- Concrete log-volume (Cor 5.10(i) notation). -/
noncomputable def cor510LogVolume (A : Set concreteLogShellField) : ℝ :=
  Real.log (cor510Volume A)

/-- The actual unit-reference log-shell has Haar mass exactly 1. -/
theorem cor510_sourceHullHaar_unit :
    sourceHullHaar
      (integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)
        : Set concreteLogShellField) = 1 :=
  sourceHullHaar_integralLogShell_eq_one

/-- **Cor 5.10 (i) Finite Log-volume, concrete p-adic side:** the source log-shell
has finite Haar mass (mass 1 < top). -/
theorem cor510_logShell_finite :
    sourceHullHaar
      (integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)
        : Set concreteLogShellField) < ⊤ := by
  rw [cor510_sourceHullHaar_unit]
  exact ENNReal.one_lt_top

/-- **Cor 5.10 (i) positivity:** the source log-shell has positive Haar mass. -/
theorem cor510_logShell_pos :
    0 < sourceHullHaar
      (integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)
        : Set concreteLogShellField) := by
  rw [cor510_sourceHullHaar_unit]
  exact zero_lt_one

/-- **Cor 5.10 (i) finite log-volume:** the unit-reference log-volume is 0. -/
theorem cor510_logVolume_unit :
    cor510LogVolume
      (integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)
        : Set concreteLogShellField) = 0 := by
  unfold cor510LogVolume cor510Volume
  rw [cor510_sourceHullHaar_unit]
  simp

/-- Cor 5.10 statement rows: (part, statement, corpus, status). -/
def cor510Rows : List (String × String × String × String) :=
  [ ("(i)", "Finite Log-volume", "corpus 8587-8593",
      "concrete p-adic side PROVED (cor510_logShell_finite/cor510_logVolume_unit)")
  , ("(ii)", "Log-Frobenius Compatibility of Log-volumes", "corpus 8594-8598",
      "dictionary statement; log-homotopy compatibility NOT formalized")
  , ("(iii)", "Panalocalization", "corpus 8599-8601",
      "dictionary statement; panalocalization morphism NOT formalized")
  , ("(iv)", "Mono-analyticization", "corpus 8602-8610",
      "dictionary statement; mono-analyticization functor NOT formalized") ]

/-- The Cor 5.10 row list has four parts. -/
theorem cor510Rows_length : cor510Rows.length = 4 := rfl

#check cor510Volume
#check cor510LogVolume
#check cor510_logShell_finite
#check cor510_logShell_pos
#check cor510_logVolume_unit
#check cor510Rows_length

end LeanFormal.IUT.XiFPaper.AbsTopIII03Cor510Actual
end