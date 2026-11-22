import tmp.sheaf.xif.paper.S2324S2135DecideActual
import tmp.sheaf.xif.paper.S2232Layer1PrimeAlignmentActual

/-! # S2331: audit of concrete S1730/S1667 models for S2135

The concrete S1730 bad set consists of the rational places 3,5,7, all inside
primeStrip 2 7.  Hence every model whose bad F-place lies over the concrete
S1730 bad set satisfies S2135; no counterexample comes from these concrete
places.  The source constraints themselves allow primes above 7, but no full
concrete T over such a place is available. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2331S2135ModelsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2232Layer1PrimeAlignmentActual
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual
open LeanFormal.IUT.XiFPaper.S2324S2135DecideActual
open LeanFormal.IUT.XiFPaper.S1730BadSetWithoutLActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}

theorem s2331_concrete_bad_residue_mem_primeStrip
    (p : NumberField.FinitePlace ℚ)
    (hp : p ∈ S1730VModBad l) :
    residueCharacteristic p ∈ primeStrip 2 7 :=
  s2232_concrete_bad_residue_mem_primeStrip l p hp

/-- A model whose bad moduli place is one of the concrete S1730 bad places. -/
structure S2331S1730Model
    (l : PrimeGeFive) where
  T : SourceNativeInitialThetaData.{0} l
  b : Bad (nativePlaceSelection T)
  p : NumberField.FinitePlace ℚ
  bad_mem : p ∈ S1730VModBad l
  residue_eq : residueCharacteristic b.1 = residueCharacteristic p

/-- Every S1730 concrete model satisfies S2135. -/
theorem s2331_S2135_of_S1730Model
    (M : S2331S1730Model l) :
    S2135PrimeAlignmentRequired M.T M.b :=
  s2232_qVFamTensorP_mem_of_residueCharacteristic_mem M.T M.b (by
    rw [M.residue_eq]
    exact s2331_concrete_bad_residue_mem_primeStrip M.p M.bad_mem)

/-- The concrete S1730 places therefore cannot refute S2135. -/
theorem s2331_no_counterexample_from_S1730
    (M : S2331S1730Model l) :
    ¬ ¬ S2135PrimeAlignmentRequired M.T M.b :=
  not_not_intro (s2331_S2135_of_S1730Model M)

/-- The source constraints alone still allow primes outside the strip; this is
the arithmetic reason a counterexample is not ruled out by the clauses. -/
theorem s2331_source_allows_outside_strip :
    ∃ p : ℕ, Nat.Prime p ∧ Odd p ∧ Nat.Coprime p l.value ∧
      p ∉ primeStrip 2 7 :=
  s2232_source_constraints_do_not_force_strip l

/-- Exact missing object: a full concrete T with a bad place of residue
characteristic > 7, giving the S2324 counterexample. -/
structure S2331CounterexampleTRequired
    (l : PrimeGeFive) where
  T : SourceNativeInitialThetaData.{0} l
  b : Bad (nativePlaceSelection T)
  gt_seven : 7 < qVFamTensorP T b
  
def S2331CounterexampleTRequiredProp : Prop :=
  Nonempty (S2331CounterexampleTRequired l)

theorem s2331_counterexample_refutes
    (C : S2331CounterexampleTRequired l) :
    ¬ S2135PrimeAlignmentRequired C.T C.b :=
  (s2324_not_strip_iff_gt_seven C.T C.b).mpr C.gt_seven

#check s2331_concrete_bad_residue_mem_primeStrip
#check S2331S1730Model
#check s2331_S2135_of_S1730Model
#check s2331_no_counterexample_from_S1730
#check s2331_source_allows_outside_strip
#check S2331CounterexampleTRequired
#check s2331_counterexample_refutes

end LeanFormal.IUT.XiFPaper.S2331S2135ModelsActual
end
