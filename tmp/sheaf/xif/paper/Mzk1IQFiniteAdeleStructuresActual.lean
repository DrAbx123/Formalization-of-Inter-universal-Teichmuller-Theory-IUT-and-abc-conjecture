import tmp.sheaf.xif.paper.Mzk1IQFiniteAdeleRestrictedActual
import Mathlib.Tactic

/-! # B#2 structures on the Mathlib finite adele ring carrier

Built on the definition-level identification IQCarrier = FiniteAdeleRing (𝓞K) K:
* unit group as units of the carrier, transported to FiniteAdeleRing units;
* principal divisor support via actual HeightOneSpectrum valuation support;
* label map interface (actual place -> label) as named input, with finite fibers
  on the principal support.
-/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1IQFiniteAdeleStructuresActual

open LeanFormal.IUT.XiFPaper.Mzk1IQFiniteAdeleRestrictedActual
open IsDedekindDomain

variable (K : Type) [Field K] [NumberField K]

/-- The Mathlib finite adele ring abbreviated. -/
abbrev iqFiniteAdeleRing : Type :=
  IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K

/-- Unit group of the IQ carrier. -/
abbrev IQUnitGroup : Type := (IQFiniteAdeleProductCarrier K)ˣ

/-- Unit group is the unit group of the finite adele ring. -/
noncomputable def iqUnitGroupEquiv : IQUnitGroup K ≃* (iqFiniteAdeleRing K)ˣ :=
  MulEquiv.refl _

/-- The canonical diagonal embedding K -> finite adeles. -/
noncomputable def principalFiniteAdele (k : K) : iqFiniteAdeleRing K :=
  IsDedekindDomain.FiniteAdeleRing.algebraMap (NumberField.RingOfIntegers K) K k

/-- The actual support of a principal finite adele: places where k is not integral. -/
noncomputable def principalSupport (k : K) :
    Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  (IsDedekindDomain.HeightOneSpectrum.Support.finite
    (R := NumberField.RingOfIntegers K) k).toFinset

/-- Membership in the principal support is exactly non-integrality. -/
theorem mem_principalSupport_iff (k : K)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    v ∈ principalSupport K k ↔
      1 < v.valuation K k := by
  unfold principalSupport IsDedekindDomain.HeightOneSpectrum.Support
  simp

/-- Paper label map: actual finite place -> label.  This is a named input; the
paper's label identification is not canonical. -/
structure PaperLabelMap (Label : Type) where
  labelOf : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → Label

/-- The label image of the principal support is finite. -/
theorem principalSupport_labelImage_finite
    {Label : Type} (L : PaperLabelMap K Label) (k : K) :
    Set.Finite (L.labelOf '' (principalSupport K k : Set _)) :=
  (principalSupport K k).finite_toSet.image L.labelOf

#check IQUnitGroup
#check iqUnitGroupEquiv
#check principalFiniteAdele
#check principalSupport
#check mem_principalSupport_iff
#check PaperLabelMap
#check principalSupport_labelImage_finite

/-- Extract the integer exponent from the actual value group. -/
noncomputable def valuationInt (k : K)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : Int :=
  let val := v.valuation K k
  if h : val = 0 then 0 else (WithZero.unzero h).toAdd

/-- Reciprocal support: non-integrality of k^{-1}. -/
noncomputable def reciprocalSupport (k : K) :
    Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  principalSupport K k⁻¹

/-- Full divisor support: union of positive and reciprocal supports. -/
noncomputable def divisorSupport (k : K) :
    Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) := by
  classical
  exact principalSupport K k ∪ reciprocalSupport K k

/-- Full principal divisor as a finitely supported integer formal sum on the union
of the actual support of k and the actual reciprocal support of k^{-1}. -/
noncomputable def principalDivisorFull (k : K) :
    (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →₀ Int :=
  ∑ v ∈ divisorSupport K k, Finsupp.single v (valuationInt K k v)

/-- Evaluation at a place in the divisor support. -/
theorem principalDivisorFull_apply_mem (k : K)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hv : v ∈ divisorSupport K k) :
    principalDivisorFull K k v = valuationInt K k v := by
  classical
  unfold principalDivisorFull
  rw [Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b _ hbv
    simp [Finsupp.single_apply, hbv]
  · intro hnot
    exact absurd hv hnot

/-- Evaluation at a place outside the divisor support. -/
theorem principalDivisorFull_apply_not_mem (k : K)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hv : v ∉ divisorSupport K k) :
    principalDivisorFull K k v = 0 := by
  classical
  have hzero : ∀ b ∈ divisorSupport K k,
      (Finsupp.single b (valuationInt K k b) :
        (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →₀ Int) v = 0 := by
    intro b hb
    have hbv : b ≠ v := by
      intro h; subst h; exact hv hb
    simp [Finsupp.single_apply, hbv]
  rw [principalDivisorFull, Finsupp.finset_sum_apply]
  exact Finset.sum_eq_zero hzero

/-- The full principal divisor has finite support contained in divisorSupport. -/
theorem principalDivisorFull_support_subset (k : K) :
    (principalDivisorFull K k).support ⊆ divisorSupport K k := by
  classical
  intro v hv
  by_contra hnot
  have h := principalDivisorFull_apply_not_mem K k v hnot
  rw [Finsupp.mem_support_iff] at hv
  exact hv h

#check valuationInt
#check reciprocalSupport
#check divisorSupport
#check principalDivisorFull
#check principalDivisorFull_apply_mem
#check principalDivisorFull_apply_not_mem
#check principalDivisorFull_support_subset

end LeanFormal.IUT.XiFPaper.Mzk1IQFiniteAdeleStructuresActual
end
