import tmp.sheaf.xif.paper.S2696VbadActual
import tmp.sheaf.xif.paper.S2689SourceBadQAbsLogActual
import tmp.sheaf.xif.paper.S2702FourPlaceDataActual
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2689SourceBadQAbsLogActual
open LeanFormal.IUT.XiFPaper.S2702FourPlaceDataActual
local instance s2701GI : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
structure R (D : S2696FourPlaceData) : Prop where
  h5 : residueCharacteristic D.p5a = 5
  h2161 : residueCharacteristic D.p2161a = 2161
noncomputable def qq (l : PrimeGeFive) (D : S2696FourPlaceData) :
    (p : NumberField.FinitePlace GaussianField) → p ∈ S2696Vbad D → Real :=
  fun p hp => |Real.log (badPlaceQProxy (S2696Selection l D) ⟨p, hp⟩)|
theorem m5 (D) : D.p5a ∈ S2696Vbad D := Or.inl rfl
theorem m2161 (D) : D.p2161a ∈ S2696Vbad D := Or.inr (Or.inr (Or.inl rfl))
theorem l5 (l) (D) (h : residueCharacteristic D.p5a = 5) :
    Real.log 5 ≤ qq l D D.p5a (m5 D) := by
  have hb := log_residueCharacteristic_le_abs_log_badPlaceQProxy
    (S2696Selection l D) (⟨D.p5a, m5 D⟩ : Bad (S2696Selection l D))
  have hb' : Real.log ((residueCharacteristic D.p5a : Nat) : Real) ≤
      |Real.log (badPlaceQProxy (S2696Selection l D) ⟨D.p5a, m5 D⟩)| := hb
  have hc : ((residueCharacteristic D.p5a : Nat) : Real) = 5 := by rw [h]; norm_num
  rw [hc] at hb'
  simpa [qq] using hb'
theorem l2161 (l) (D) (h : residueCharacteristic D.p2161a = 2161) :
    Real.log 2161 ≤ qq l D D.p2161a (m2161 D) := by
  have hb := log_residueCharacteristic_le_abs_log_badPlaceQProxy
    (S2696Selection l D) (⟨D.p2161a, m2161 D⟩ : Bad (S2696Selection l D))
  have hb' : Real.log ((residueCharacteristic D.p2161a : Nat) : Real) ≤
      |Real.log (badPlaceQProxy (S2696Selection l D) ⟨D.p2161a, m2161 D⟩)| := hb
  have hc : ((residueCharacteristic D.p2161a : Nat) : Real) = 2161 := by rw [h]; norm_num
  rw [hc] at hb'
  simpa [qq] using hb'
theorem lower (l) (D) (hr : R D) : Real.log 5 + Real.log 2161 ≤ S2696BadQAbsLog D (qq l D) := by
  classical
  unfold S2696BadQAbsLog
  letI : Fintype {p : NumberField.FinitePlace GaussianField // p ∈ S2696Vbad D} := (S2696Vbad_finite D).fintype
  let a : {p : NumberField.FinitePlace GaussianField // p ∈ S2696Vbad D} := ⟨D.p5a, m5 D⟩
  let b : {p : NumberField.FinitePlace GaussianField // p ∈ S2696Vbad D} := ⟨D.p2161a, m2161 D⟩
  have hne : NumberFieldFinitePlace.residueCharacteristic D.p5a ≠ NumberFieldFinitePlace.residueCharacteristic D.p2161a := by rw [hr.h5, hr.h2161]; norm_num
  have hab : a ≠ b := by
    intro h
    exact hne (congrArg (fun x : {p : NumberField.FinitePlace GaussianField // p ∈ S2696Vbad D} => NumberFieldFinitePlace.residueCharacteristic x.1) h)
  have hnonneg : ∀ x : {p : NumberField.FinitePlace GaussianField // p ∈ S2696Vbad D}, 0 ≤ qq l D x.1 x.2 := fun x => abs_nonneg _
  have hpair : qq l D a.1 a.2 + qq l D b.1 b.2 ≤ ∑ x : {p : NumberField.FinitePlace GaussianField // p ∈ S2696Vbad D}, qq l D x.1 x.2 := by
    have hEq : (∑ x ∈ ({a, b} : Finset {p : NumberField.FinitePlace GaussianField // p ∈ S2696Vbad D}), qq l D x.1 x.2) = qq l D a.1 a.2 + qq l D b.1 b.2 := Finset.sum_pair hab
    rw [← hEq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (by intro x _; exact Finset.mem_univ x) (by intro x _ _; exact hnonneg x)
  have h1 := l5 l D hr.h5
  have h2 := l2161 l D hr.h2161
  linarith
#check lower
end
