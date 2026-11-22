import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianIntegralBasis
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

noncomputable section
set_option maxRecDepth 100000
namespace ProbeGaussPrime
def piPlus : GaussianInt := ⟨44, 15⟩
#check Ideal.absNorm_span_singleton
#check Algebra.norm
#check Zsqrtd.norm
#check Zsqrtd.norm_eq_mul_conj
#check Zsqrtd.norm_def
#check Zsqrtd.normMonoidHom
example : ((Algebra.norm ℤ) piPlus).natAbs = 2161 := by
  simp [piPlus, Zsqrtd.norm_def]
end ProbeGaussPrime
end
