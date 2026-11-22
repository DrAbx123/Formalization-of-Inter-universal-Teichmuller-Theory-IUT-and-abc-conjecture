import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianIntegralBasis
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

noncomputable section
open LeanFormal.IUT
set_option maxRecDepth 100000
namespace ProbeGaussPrime

def piPlus : GaussianInt := ⟨44, 15⟩

example : Zsqrtd.norm piPlus = 2161 := by
  rw [Zsqrtd.norm_def]
  norm_num [piPlus]

example : Ideal.absNorm (Ideal.span {piPlus}) = 2161 := by
  rw [Ideal.absNorm_span_singleton]
  norm_num [piPlus, Zsqrtd.norm_def]

example : Nat.Prime 2161 := by decide

end ProbeGaussPrime
end
