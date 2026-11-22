import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace

namespace LeanFormal.IUT.XiFPaper.S2687Probe

def concrete2161Prime : Nat.Primes := ⟨2161, by norm_num⟩

noncomputable def concrete2161HeightOne :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm
    concrete2161Prime

noncomputable def concrete2161Place : NumberField.FinitePlace ℚ :=
  NumberField.FinitePlace.mk concrete2161HeightOne

theorem concrete2161HeightOne_natGenerator :
    Rat.HeightOneSpectrum.natGenerator concrete2161HeightOne = 2161 := by
  exact congrArg (fun p : Nat.Primes => p.1)
    ((Rat.HeightOneSpectrum.primesEquiv
      (R := NumberField.RingOfIntegers ℚ)).apply_symm_apply concrete2161Prime)

#check concrete2161Place
#check concrete2161HeightOne_natGenerator

end LeanFormal.IUT.XiFPaper.S2687Probe
end
