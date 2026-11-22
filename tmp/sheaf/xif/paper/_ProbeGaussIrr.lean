import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianIntegralBasis
import Mathlib.RingTheory.DedekindDomain.Basic

noncomputable section
set_option maxRecDepth 100000
namespace ProbeGaussIrr
def piPlus : GaussianInt := ⟨44, 15⟩
theorem norm_pi : Zsqrtd.norm piPlus = 2161 := by
  rw [Zsqrtd.norm_def]; norm_num [piPlus]
theorem prime2161 : Nat.Prime 2161 := by decide
theorem irreducible_pi : Irreducible piPlus := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    have h : (Zsqrtd.norm piPlus).natAbs = 1 := (Zsqrtd.norm_eq_one_iff (d := -1)).mpr hunit
    rw [norm_pi] at h
    norm_num at h
  · intro a b hab
    have hnorm : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs = 2161 := by
      rw [← Int.natAbs_mul, ← Zsqrtd.norm_mul, ← hab, norm_pi]
      norm_num
    have hdiv : (Zsqrtd.norm a).natAbs ∣ 2161 := ⟨(Zsqrtd.norm b).natAbs, hnorm.symm⟩
    rcases prime2161.eq_one_or_self_of_dvd _ hdiv with h1 | h1
    · left
      exact (Zsqrtd.norm_eq_one_iff (d := -1)).mp h1
    · right
      have hb : (Zsqrtd.norm b).natAbs = 1 := by
        rw [h1] at hnorm
        omega
      exact (Zsqrtd.norm_eq_one_iff (d := -1)).mp hb
end ProbeGaussIrr
end
