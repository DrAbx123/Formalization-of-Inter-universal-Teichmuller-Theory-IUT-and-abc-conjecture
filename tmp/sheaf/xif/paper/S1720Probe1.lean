import tmp.sheaf.xif.paper.S1708NinePointInjectionActual
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import Mathlib.FieldTheory.Normal.Basic

noncomputable section
open Polynomial WeierstrassCurve
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual

namespace Probe1

def P1 : ℚ[X] := X ^ 2 + 1

def f1 : ℚ[X] := S1687H * P1

abbrev Field1 : Type := Polynomial.SplittingField f1

local instance : DecidableEq Field1 := Classical.decEq _

instance : NumberField Field1 where
  to_charZero := inferInstance
  to_finiteDimensional := by
    letI : IsSplittingField ℚ Field1 f1 := Polynomial.IsSplittingField.splittingField f1
    exact Polynomial.IsSplittingField.finiteDimensional Field1 f1

example : IsSplittingField ℚ Field1 f1 := Polynomial.IsSplittingField.splittingField f1

theorem f1_splits : (f1.map (algebraMap ℚ Field1)).Splits :=
  Polynomial.SplittingField.splits f1

theorem P1_splits : (P1.map (algebraMap ℚ Field1)).Splits := by
  have hf : ((S1687H * P1).map (algebraMap ℚ Field1)).Splits := by
    simpa [f1] using f1_splits
  rw [Polynomial.map_mul] at hf
  rw [Polynomial.splits_mul'] at hf
  exact hf.2.resolve_right (by
    intro h
    have hmap : S1687H.map (algebraMap ℚ Field1) = 0 := h
    exact S1687H_map_ne_zero (by simpa using hmap))

theorem P1_degree : P1.degree = (2 : WithBot ℕ) := by
  unfold P1
  compute_degree!

example : HasSqrtNegOne Field1 := by
  have hdeg : (P1.map (algebraMap ℚ Field1)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (algebraMap ℚ Field1).injective, P1_degree]
    norm_num
  let r : Field1 := Polynomial.rootOfSplits P1_splits hdeg
  have hr : Polynomial.eval r (P1.map (algebraMap ℚ Field1)) = 0 :=
    Polynomial.eval_rootOfSplits P1_splits hdeg
  have hr' : Polynomial.aeval r P1 = 0 := by
    simpa [Polynomial.aeval_def, Polynomial.eval_map] using hr
  refine ⟨r, ?_⟩
  have h : r ^ 2 + 1 = 0 := by
    simpa [P1] using hr'
  rw [pow_two] at h
  linear_combination h

end Probe1
