import tmp.sheaf.xif.paper.ArithmeticLineBundleActual
import tmp.sheaf.xif.paper.QPilotGlobalIdealActual
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
import Mathlib.RingTheory.DedekindDomain.Factorization

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2735QPilotIdealSupportGateActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.N8Closure.QPilotGlobalIdealActual
open LeanFormal.IUT.NumberFieldFinitePlace

local instance s2735FivePrime : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance s2735Prime2161 : Fact (Nat.Prime 2161) := ⟨by norm_num⟩

variable {l : PrimeGeFive} (A : InitialThetaArithmeticData l)

abbrev S2735O : Type := SourceOK (A := A)

/-- The finite prime support of a fractional ideal, via the actual Dedekind
valuation counts. -/
def S2735IdealSupport (I : SourceLineBundle (A := A)) :
    Set (IsDedekindDomain.HeightOneSpectrum (S2735O (A := A))) :=
  {v | FractionalIdeal.count A.K v I ≠ 0}

/-- The target bad support: height-one primes over the rational primes 5 and 2161. -/
def S2735VbadSupport :
    Set (IsDedekindDomain.HeightOneSpectrum (S2735O (A := A))) :=
  {v | v.asIdeal.LiesOver (Ideal.span {(5 : ℤ)}) ∨
    v.asIdeal.LiesOver (Ideal.span {(2161 : ℤ)})}

/-- The unit line bundle has empty finite prime support. -/
theorem S2735_unitLineBundle_support_eq_empty :
    S2735IdealSupport (A := A) (unitLineBundle (A := A)) = ∅ := by
  ext v
  simp [S2735IdealSupport, unitLineBundle, FractionalIdeal.count_one]

/-- The bad support is nonempty: a height-one prime over (5) exists by the
actual lying-over theorem for the integral extension ℤ → O_K. -/
theorem S2735VbadSupport_nonempty :
    (S2735VbadSupport (A := A)).Nonempty := by
  haveI h5max : (Ideal.span {(5 : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 5
  let O := S2735O (A := A)
  haveI s2735FactFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : (Ideal.span {(5 : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 5
  let P := Classical.choose
    (Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := O) (R := ℤ) (Ideal.span {(5 : ℤ)}))
  have hPmax : P.IsMaximal :=
    (Classical.choose_spec
      (Ideal.exists_maximal_ideal_liesOver_of_isIntegral
        (S := O) (R := ℤ) (Ideal.span {(5 : ℤ)}))).1
  have hPlies : P.LiesOver (Ideal.span {(5 : ℤ)}) :=
    (Classical.choose_spec
      (Ideal.exists_maximal_ideal_liesOver_of_isIntegral
        (S := O) (R := ℤ) (Ideal.span {(5 : ℤ)}))).2
  let v : IsDedekindDomain.HeightOneSpectrum O :=
    { asIdeal := P
      isPrime := hPmax.isPrime
      ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField hPmax
        (NumberField.RingOfIntegers.not_isField A.K) }
  exact ⟨v, Or.inl hPlies⟩

/-- Unit-line-bundle substitution is impossible: its empty support is not the
bad support. -/
theorem S2735_unitLineBundle_support_ne_vbad :
    S2735IdealSupport (A := A) (unitLineBundle (A := A)) ≠
      S2735VbadSupport (A := A) := by
  rw [S2735_unitLineBundle_support_eq_empty]
  intro h
  have hne := S2735VbadSupport_nonempty (A := A)
  rw [← h] at hne
  exact hne.ne_empty rfl

/-- Exact object gate for a genuine q-pilot ideal with bad support: the ideal
must be a principal q-pilot ideal, its finite support must be exactly Vbad, and
it must not be the unit ideal. -/
structure QPilotVbadIdealData where
  lift : GlobalQPilotLift (A := A)
  support_eq : S2735IdealSupport (A := A)
      ((qPilotIdealOfLift (A := A) lift :
        Ideal (S2735O (A := A))) :
        FractionalIdeal (nonZeroDivisors (S2735O (A := A))) A.K) =
    S2735VbadSupport (A := A)
  not_unit : qPilotIdealOfLift (A := A) lift ≠ ⊤

theorem QPilotVbadIdealData_not_unit (D : QPilotVbadIdealData (A := A)) :
    qPilotIdealOfLift (A := A) D.lift ≠ ⊤ := D.not_unit

theorem QPilotVbadIdealData_support (D : QPilotVbadIdealData (A := A)) :
    S2735IdealSupport (A := A)
      ((qPilotIdealOfLift (A := A) D.lift :
        Ideal (S2735O (A := A))) :
        FractionalIdeal (nonZeroDivisors (S2735O (A := A))) A.K) =
    S2735VbadSupport (A := A) := D.support_eq

#check S2735IdealSupport
#check S2735VbadSupport
#check S2735_unitLineBundle_support_eq_empty
#check S2735VbadSupport_nonempty
#check S2735_unitLineBundle_support_ne_vbad
#check QPilotVbadIdealData
#print axioms S2735_unitLineBundle_support_ne_vbad
end LeanFormal.IUT.XiFPaper.S2735QPilotIdealSupportGateActual
end
