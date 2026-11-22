import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianIntegralBasis
#synth Algebra ℤ GaussianInt
#check (Algebra.norm ℤ : GaussianInt →* ℤ)
#check Zsqrtd.normMonoidHom
example : (Algebra.norm ℤ : GaussianInt →* ℤ) = Zsqrtd.normMonoidHom := by
  ext x
  sorry
