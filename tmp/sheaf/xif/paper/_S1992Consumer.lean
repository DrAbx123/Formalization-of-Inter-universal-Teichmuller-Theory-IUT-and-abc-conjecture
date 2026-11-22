import tmp.sheaf.xif.paper.S1992RebasedLocalInputActual

noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.S1992RebasedLocalInputActual

/-- The concrete Gaussian field instances, as in the S1895/S1527 files: they are
proved facts about `X^2 + 1` over `ℚ`, not assumptions. -/
local instance s1992ConsumerGaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1992ConsumerFivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

namespace LeanFormal.IUT.XiFPaper.S1992Consumer

variable (D : S1895PaperInput)

/-- The family datum is exactly S1978's missing rebased input. -/
example : Nonempty (S1978RebasedPaperInput D) ↔
    Nonempty (S1992RebasedLocalFamily D) :=
  S1992RebasedLocalFamily.nonempty_iff_rebasedPaperInput D

/-- An inhabitant gives S1978's rebased input, with the actual local strip at
`(1,0)`. -/
example (E : S1992RebasedLocalFamily D) :
    E.toRebasedInput.input.fPrimeStripAt 1 0 = localOFieldStrip :=
  E.toRebasedInput.core_eq_local

/-- An inhabitant gives S1978's rebased paper q-pilot object. -/
example (E : S1992RebasedLocalFamily D) : S1978RebasedPaperO D :=
  S1992RebasedPaperO D E

/-- Its strip is the actual local `O^×` strip. -/
example (E : S1992RebasedLocalFamily D) :
    (S1992RebasedPaperO D E).object.strip = localOFieldStrip :=
  S1992RebasedPaperO_strip D E

/-- Its q-pilot scalar is the actual completion magnitude. -/
example (E : S1992RebasedLocalFamily D) :
    (S1992RebasedPaperO D E).object.qPilotLogVolume =
      -localLogMagnitude S1487Cand :=
  S1992RebasedPaperO_qPilot_eq D E

/-- All four paper-level identifications hold on the rebased paper object. -/
example (E : S1992RebasedLocalFamily D) :
    (S1992RebasedPaperO D E).object.paper_strip_identification ∧
      (S1992RebasedPaperO D E).object.paper_logKummer_identification ∧
      (S1992RebasedPaperO D E).object.paper_lineBundle_identification ∧
      (S1992RebasedPaperO D E).object.paper_qPilot_log_identification :=
  ⟨S1992RebasedPaperO_paper_strip D E, S1992RebasedPaperO_paper_logKummer D E,
    S1992RebasedPaperO_paper_lineBundle D E, S1992RebasedPaperO_paper_qPilot D E⟩

/-- Neither the S1895 input nor its paper object carries the local strip. -/
example : (S1895PaperInput.I D).fPrimeStripAt 1 0 ≠ localOFieldStrip :=
  s1895Input_not_rebased D

example (E : S1992RebasedLocalFamily D) :
    (S1992RebasedPaperO D E).object.strip ≠ (S1895PaperO D).strip :=
  S1992RebasedPaperO_strip_ne_s1895 D E

/-- The family must really vary: it cannot be constant on the local strip, and
it contains two distinct compatible local strips. -/
example (E : S1992RebasedLocalFamily D) :
    ∃ i j : E.family.index, i ≠ j ∧
      (E.family.theater i).primeStrip ≠ (E.family.theater j).primeStrip :=
  E.exists_distinct_strips

/-- Every member's strip is compatible with the actual local strip. -/
example (E : S1992RebasedLocalFamily D) (i : E.family.index) :
    Nonempty (FPrimeStripEquiv localOFieldStrip
      (E.family.theater i).primeStrip) :=
  E.other_strip_linked i

/-- Compatible local strips have trivial degree (no degree freedom). -/
example (S : FPrimeStrip PaperV) (φ : FPrimeStripEquiv localOFieldStrip S)
    (v : PaperV) (x : S.Mon v) : S.degree v x = 1 :=
  linked_degree_trivial S φ v x

/-- The shear family cannot host the local strip. -/
example (S : SourceDefinition31Data.{0} D.l)
    (T : HodgeTheater.{0, 0, 0, 0} D.l PaperV)
    (hT : T.primeStrip = localOFieldStrip) :
    ¬ Nonempty (HodgeTheaterLink T ((S1487OriginalInput S).theaterAt 1 0)) :=
  no_link_from_local_to_shear_input S hT

end LeanFormal.IUT.XiFPaper.S1992Consumer
