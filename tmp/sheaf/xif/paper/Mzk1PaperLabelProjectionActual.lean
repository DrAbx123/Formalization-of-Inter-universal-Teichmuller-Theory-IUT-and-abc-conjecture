import tmp.sheaf.xif.paper.Mzk1IQFiniteAdeleStructuresActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import Mathlib.Tactic

/-! # B#2 semantic: candidate label projections from actual finite places

Actual data:
* a finite place v has the underlying rational prime ideal v.asIdeal.under ℤ;
* its absolute norm is a natural number (the rational prime for a place of a
  number field).
* the paper label group is exactly ProcessionLabel l = (ZMod l.value)^x.

Constructed here: a natural-number projection and a candidate map into the
paper label group on places whose rational prime is nonzero mod l.

Exact GAP: there is no canonical map from finite places to paper theta labels
in T.arithmetic; the paper label group is not a residue-character group.  The
candidate map below is NOT asserted to be the paper label identification.
-/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperLabelProjectionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual

variable (K : Type) [Field K] [NumberField K]

/-- The underlying rational prime ideal is v.asIdeal.under ℤ. -/
noncomputable def rationalPrimeIdealOfFinitePlace
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Ideal Int :=
  v.asIdeal.under Int

/-- The absolute norm of the underlying rational prime ideal. -/
noncomputable def rationalPrimeOfFinitePlace
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : Nat :=
  Ideal.absNorm (rationalPrimeIdealOfFinitePlace K v)

/-- Definitional form of the rational-prime projection. -/
theorem rationalPrimeOfFinitePlace_eq
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    rationalPrimeOfFinitePlace K v =
      Ideal.absNorm (v.asIdeal.under Int) := rfl

variable {K}

/-- The paper label group type, written explicitly. -/
abbrev PaperLabelGroup (l : PrimeGeFive) : Type := ProcessionLabel l

/-- Candidate map to the paper label group on places with nonzero rational
prime mod l.  This is a residue-prime construction, not the paper theta-label
identification. -/
def candidateLabelOfPlace
    (l : PrimeGeFive)
    (v : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
      ((rationalPrimeOfFinitePlace K v : Nat) : ZMod l.value) ≠ 0}) :
    PaperLabelGroup l := by
  classical
  haveI : Fact (Nat.Prime l.value) := ⟨l.prime⟩
  let x : ZMod l.value := ((rationalPrimeOfFinitePlace K (v : _) : Nat) : ZMod l.value)
  exact Units.mk0 x v.2

/-- Exact label-interface gap: a paper label projection is a map from finite
places to ProcessionLabel l; no such canonical map is produced by the actual
arithmetic data. -/
structure PaperLabelProjectionInterface (l : PrimeGeFive) where
  labelOf : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) →
    PaperLabelGroup l

#check rationalPrimeIdealOfFinitePlace
#check rationalPrimeOfFinitePlace
#check rationalPrimeOfFinitePlace_eq
#check PaperLabelGroup
#check candidateLabelOfPlace
#check PaperLabelProjectionInterface
end LeanFormal.IUT.XiFPaper.Mzk1PaperLabelProjectionActual
end
