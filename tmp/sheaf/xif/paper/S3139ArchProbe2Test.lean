import LeanFormal.IUT.Foundations.AlgebraicGeometry.InfinitePlaceLogDictionary
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.XiFPaper.S3139ArchProbe2Test

open LeanFormal.IUT
open LeanFormal.IUT.InfinitePlaceLogDictionary

universe u v ua uv upi umon ui

variable {l : PrimeGeFive}

example (A : InitialThetaArithmeticData.{u} l) (v : NumberField.InfinitePlace A.Fmod) :
    Type u := v.Completion

example (A : InitialThetaArithmeticData.{u} l) (v : NumberField.InfinitePlace A.Fmod) :
    (A.Fmod)ˣ →* (v.Completion)ˣ :=
  Units.map (algebraMap A.Fmod v.Completion).toMonoidHom

example (A : InitialThetaArithmeticData.{u} l) (v : NumberField.InfinitePlace A.Fmod)
    (u : (A.Fmod)ˣ) : ℝ :=
  infinitePlaceLog v (Additive.ofMul (Units.map
    (algebraMap A.Fmod v.Completion).toMonoidHom u))

example (A : InitialThetaArithmeticData.{u} l) (v : NumberField.InfinitePlace A.Fmod) :
    Additive (v.Completion)ˣ →+ ℝ := infinitePlaceLog v

end LeanFormal.IUT.XiFPaper.S3139ArchProbe2Test
