import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm

/-!
# Mzk1PStarScaleActual — p* invariants and their concrete log-shell scale identification

STEP 0 prior-art: SourceLogShellCarrier (sourceLogShellStar := p if p odd else p^2),
SourceLocalLogShellDatum (sourceLogShellStar_eq_logShellScale for primes) -> REUSE; this file
re-exports and derives the p* facts used by Prop 5.8(i) (p*, positivity, p=2 value, odd case,
and the concrete log-shell scale identification).

No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PStarScaleActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm

/-- For primes, the source p* equals the concrete log-shell scale (tree dictionary). -/
theorem pStar_eq_logShellScale {p : ℕ} (hp : p.Prime) :
    sourceLogShellStar p = logShellScale p :=
  sourceLogShellStar_eq_logShellScale hp

/-- p* is positive for positive p. -/
theorem pStar_pos {p : ℕ} (hp : 0 < p) : 0 < sourceLogShellStar p :=
  sourceLogShellStar_pos hp

/-- For p = 2 the paper's p* is p^2 = 4. -/
theorem pStar_two : sourceLogShellStar 2 = 4 := by
  decide

/-- For an odd prime p, the paper's p* is p. -/
theorem pStar_odd_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    sourceLogShellStar p = p := by
  unfold sourceLogShellStar
  rcases hp.eq_two_or_odd with h | h
  · exact absurd h h2
  · simp [h]

/-- p* equals the paper's case split for all primes. -/
theorem pStar_eq_paperPStar {p : ℕ} (hp : p.Prime) :
    sourceLogShellStar p = if p = 2 then p ^ 2 else p := by
  unfold sourceLogShellStar
  rcases hp.eq_two_or_odd with h | h
  · rw [h]
    decide
  · have h2 : p ≠ 2 := by intro hh; subst hh; norm_num at h
    simp [h2, h]

/-- p* row record: (item, statement, status). -/
def pStarRows : List (String × String × String) :=
  [ ("p* = concrete log-shell scale", "sourceLogShellStar p = logShellScale p for prime p", "PROVED (tree re-export)"),
    ("p* positivity", "0 < sourceLogShellStar p for 0 < p", "PROVED (tree re-export)"),
    ("p = 2 case", "sourceLogShellStar 2 = 4", "PROVED"),
    ("odd prime case", "sourceLogShellStar p = p for odd prime p", "PROVED"),
    ("paper case split", "sourceLogShellStar p = if p = 2 then p^2 else p", "PROVED") ]

/-- The p* row record has five rows. -/
theorem pStarRows_length : pStarRows.length = 5 := rfl

#check pStar_eq_logShellScale
#check pStar_pos
#check pStar_two
#check pStar_odd_prime
#check pStar_eq_paperPStar
#check pStarRows_length

end LeanFormal.IUT.XiFPaper.Mzk1PStarScaleActual
end
