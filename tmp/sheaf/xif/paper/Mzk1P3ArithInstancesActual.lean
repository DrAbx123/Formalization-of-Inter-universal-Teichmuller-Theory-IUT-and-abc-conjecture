/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import Mathlib.Tactic

/-! # P3 arithmetic instances for the actual source tower `A : InitialThetaArithmeticData`

Constructs (or records as Mathlib-provided) the instances required by the final P3
assembly.  Stated for a generic `A : InitialThetaArithmeticData l`, so they resolve at
`T.arithmetic` automatically. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3ArithInstancesActual

open LeanFormal.IUT
open NumberField
open scoped NumberField

variable {l : PrimeGeFive}
variable (A : InitialThetaArithmeticData l)

/-- `A.K` is finite-dimensional over `A.Fmod` by the tower. -/
instance instFiniteDimensionalFmodK : FiniteDimensional A.Fmod A.K :=
  FiniteDimensional.trans A.Fmod A.F A.K

/-- `A.K` is separable over `A.Fmod` by the tower (both steps are Galois). -/
instance instSeparableFmodK : Algebra.IsSeparable A.Fmod A.K :=
  Algebra.IsSeparable.trans (F := A.Fmod) (E := A.F) (K := A.K)

/-- `𝓞 A.K` is finite over `𝓞 A.Fmod` (integral closure of an integrally closed
Noetherian ring). -/
instance instModuleFiniteRingOfIntegers :
    Module.Finite (NumberField.RingOfIntegers A.Fmod)
      (NumberField.RingOfIntegers A.K) :=
  IsIntegralClosure.finite (A := NumberField.RingOfIntegers A.Fmod)
    (K := A.Fmod) (L := A.K) (C := NumberField.RingOfIntegers A.K)

/-- Mathlib-provided instances (all `inferInstance`). -/
example : Algebra (NumberField.RingOfIntegers A.Fmod) A.K := inferInstance

example : IsScalarTower (NumberField.RingOfIntegers A.Fmod) A.Fmod A.K := inferInstance

example : IsScalarTower (NumberField.RingOfIntegers A.Fmod)
    (NumberField.RingOfIntegers A.K) A.K := inferInstance

example : IsScalarTower ℤ (NumberField.RingOfIntegers A.Fmod)
    (NumberField.RingOfIntegers A.K) := inferInstance

example : IsIntegralClosure (NumberField.RingOfIntegers A.K)
    (NumberField.RingOfIntegers A.Fmod) A.K := inferInstance

example : Module.IsTorsionFree (NumberField.RingOfIntegers A.Fmod)
    (NumberField.RingOfIntegers A.K) := inferInstance

example : Algebra.IsIntegral (NumberField.RingOfIntegers A.Fmod)
    (NumberField.RingOfIntegers A.K) := inferInstance

def arithInstanceRows : List (String × String × String) :=
  [ ("FiniteDimensional Fmod K", "FiniteDimensional.trans over Fmod-F-K", "CONSTRUCTED"),
    ("Algebra.IsSeparable Fmod K", "Algebra.IsSeparable.trans (both Galois)", "CONSTRUCTED"),
    ("Module.Finite (𝓞Fmod) (𝓞K)", "IsIntegralClosure.finite", "CONSTRUCTED"),
    ("Algebra (𝓞Fmod) K", "NumberField/Basic RingOfIntegers algebra instance", "MATHLIB inferInstance"),
    ("IsScalarTower (𝓞Fmod) Fmod K", "NumberField/Basic:121", "MATHLIB inferInstance"),
    ("IsScalarTower (𝓞Fmod) (𝓞K) K", "NumberField/Basic:352", "MATHLIB inferInstance"),
    ("IsScalarTower ℤ (𝓞Fmod) (𝓞K)", "NumberField/Basic:234", "MATHLIB inferInstance"),
    ("IsIntegralClosure (𝓞K) (𝓞Fmod) K", "NumberField/Basic:355", "MATHLIB inferInstance"),
    ("Module.IsTorsionFree (𝓞Fmod)(𝓞K)", "NumberField/Basic:381", "MATHLIB inferInstance"),
    ("Algebra.IsIntegral (𝓞Fmod)(𝓞K)", "NumberField/Basic:364", "MATHLIB inferInstance") ]

theorem arithInstanceRows_length : arithInstanceRows.length = 10 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3ArithInstancesActual

end