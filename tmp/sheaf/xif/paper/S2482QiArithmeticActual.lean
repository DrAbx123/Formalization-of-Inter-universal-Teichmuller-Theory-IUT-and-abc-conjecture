import tmp.sheaf.xif.paper.S2482QiCurveActual
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482QiArithmeticActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open Polynomial

theorem S2482_finrank : Module.finrank ℚ F = 2 := by
  have hf : (X ^ 2 + 1 : ℚ[X]) ≠ 0 := by
    intro h
    have h2 := congrArg (fun q : ℚ[X] => q.coeff 0) h
    simp at h2
  change Module.finrank ℚ (AdjoinRoot (X ^ 2 + 1 : ℚ[X])) = 2
  rw [(AdjoinRoot.powerBasis hf).finrank]
  rw [AdjoinRoot.powerBasis_dim hf]
  rw [show (X ^ 2 + 1 : ℚ[X]).natDegree = 2 by
    rw [show (1 : ℚ[X]) = C 1 by simp]
    exact Polynomial.natDegree_X_pow_add_C]

instance S2482_quadratic : Algebra.IsQuadraticExtension ℚ F where
  finrank_eq_two' := S2482_finrank

theorem S2482_isGalois : IsGalois ℚ F := by
  infer_instance

example : IsGalois F F := inferInstance
example : IsScalarTower ℚ F F := inferInstance
example : FiniteDimensional F F := inferInstance

namespace S2482Arithmetic

def l5 : PrimeGeFive where
  value := 5
  prime := by decide
  ge_five := by norm_num

instance : IsGalois ℚ F := S2482_isGalois

noncomputable def thetaTower : ThetaFieldTower l5 ℚ F F where
  sqrtNegOne := S2480_hasSqrtNegOne
  degreePrimeToL := by
    rw [S2482_finrank]
    change Nat.Coprime 2 5
    norm_num

noncomputable def arithmeticData : InitialThetaArithmeticData l5 where
  Fmod := ℚ
  F := F
  K := F
  tower := thetaTower
  curve := S2482PuncturedCurve

end S2482Arithmetic

#check S2482_finrank
#check S2482_quadratic
#check S2482_isGalois
#check S2482Arithmetic.thetaTower
#check S2482Arithmetic.arithmeticData
#print axioms S2482_finrank
#print axioms S2482Arithmetic.thetaTower
#print axioms S2482Arithmetic.arithmeticData

end LeanFormal.IUT.XiFPaper.S2482QiArithmeticActual

end