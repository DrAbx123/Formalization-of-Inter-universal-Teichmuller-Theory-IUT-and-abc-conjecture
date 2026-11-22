import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegreeGlobal

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2696VbadActual

local instance s2696GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

def S2696Prime2161 : Nat.Primes := ⟨2161, by norm_num⟩

def S2696HeightOne2161 :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm
    S2696Prime2161

def S2696Place2161 : NumberField.FinitePlace ℚ :=
  NumberField.FinitePlace.mk S2696HeightOne2161

theorem S2696HeightOne2161_natGenerator :
    Rat.HeightOneSpectrum.natGenerator S2696HeightOne2161 = 2161 :=
  congrArg (fun p : Nat.Primes => p.1)
    ((Rat.HeightOneSpectrum.primesEquiv
      (R := NumberField.RingOfIntegers ℚ)).apply_symm_apply S2696Prime2161)

theorem S2696HeightOne2161_asIdeal_eq_span :
    S2696HeightOne2161.asIdeal =
      Ideal.span {(2161 : NumberField.RingOfIntegers ℚ)} := by
  let e : NumberField.RingOfIntegers ℚ ≃+* ℤ :=
    Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)
  have h := Rat.HeightOneSpectrum.span_natGenerator
    (R := NumberField.RingOfIntegers ℚ) S2696HeightOne2161
  rw [S2696HeightOne2161_natGenerator] at h
  change Ideal.span {(2161 : ℤ)} =
    Ideal.map e.toRingHom S2696HeightOne2161.asIdeal at h
  have h' := congrArg (Ideal.map e.symm.toRingHom) h
  rw [Ideal.map_span] at h'
  simp only [Set.image_singleton] at h'
  simp at h'
  exact h'.symm

theorem S2696Place2161_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic S2696Place2161 = 2161 := by
  rw [NumberFieldFinitePlace.residueCharacteristic]
  change ringChar (NumberField.RingOfIntegers ℚ ⧸
    S2696Place2161.maximalIdeal.asIdeal) = 2161
  rw [S2696Place2161, NumberField.FinitePlace.maximalIdeal_mk]
  rw [S2696HeightOne2161_asIdeal_eq_span]
  rw [Ideal.ringChar_quot]
  have hunder : Ideal.under ℤ
      (Ideal.span {(2161 : NumberField.RingOfIntegers ℚ)}) =
      Ideal.span {(2161 : ℤ)} := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      let e : NumberField.RingOfIntegers ℚ ≃+* ℤ :=
        Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)
      have he : e (algebraMap ℤ (NumberField.RingOfIntegers ℚ) x) = x := by simp
      have hy' := congrArg e hy
      rw [map_mul, map_ofNat, he] at hy'
      exact ⟨e y, hy'⟩
    · rintro ⟨y, rfl⟩
      exact ⟨algebraMap ℤ (NumberField.RingOfIntegers ℚ) y, by
        rw [map_mul, map_ofNat]⟩
  rw [hunder, Ideal.absNorm_span_singleton]
  norm_num

noncomputable def S2696GaussianPlace2161 : NumberField.FinitePlace GaussianField :=
  Classical.choose
    (NumberFieldFinitePlace.comap_surjective
      (k := ℚ) (K := GaussianField) S2696Place2161)

theorem S2696GaussianPlace2161_comap :
    NumberFieldFinitePlace.comap (k := ℚ) S2696GaussianPlace2161 =
      S2696Place2161 :=
  Classical.choose_spec
    (NumberFieldFinitePlace.comap_surjective
      (k := ℚ) (K := GaussianField) S2696Place2161)

theorem S2696GaussianPlace2161_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic S2696GaussianPlace2161 = 2161 := by
  have h := NumberFieldFinitePlace.residueCharacteristic_comap
    (k := ℚ) (K := GaussianField) S2696GaussianPlace2161
  rw [S2696GaussianPlace2161_comap] at h
  rw [← h, S2696Place2161_residueCharacteristic]

#check S2696Place2161
#check S2696GaussianPlace2161
#check S2696GaussianPlace2161_comap
#check S2696GaussianPlace2161_residueCharacteristic

structure S2696FourPlaceData where
  p5a : NumberField.FinitePlace GaussianField
  p5b : NumberField.FinitePlace GaussianField
  p2161a : NumberField.FinitePlace GaussianField
  p2161b : NumberField.FinitePlace GaussianField
  odd5a : Odd (NumberFieldFinitePlace.residueCharacteristic p5a)
  odd5b : Odd (NumberFieldFinitePlace.residueCharacteristic p5b)
  odd2161a : Odd (NumberFieldFinitePlace.residueCharacteristic p2161a)
  odd2161b : Odd (NumberFieldFinitePlace.residueCharacteristic p2161b)

def S2696Vbad (D : S2696FourPlaceData) : Set (NumberField.FinitePlace GaussianField) :=
  {p | p = D.p5a ∨ p = D.p5b ∨ p = D.p2161a ∨ p = D.p2161b}

theorem S2696Vbad_nonempty (D : S2696FourPlaceData) :
    (S2696Vbad D).Nonempty :=
  ⟨D.p5a, Or.inl rfl⟩

theorem S2696Vbad_finite (D : S2696FourPlaceData) :
    (S2696Vbad D).Finite := by
  have h : S2696Vbad D =
      ({D.p5a} ∪ {D.p5b} ∪ {D.p2161a} ∪ {D.p2161b} :
        Set (NumberField.FinitePlace GaussianField)) := by
    ext p; constructor
    · rintro (rfl | rfl | rfl | rfl) <;> simp [S2696Vbad]
    · rintro (((rfl | rfl) | rfl) | rfl) <;> simp [S2696Vbad]
  rw [h]
  exact (((Set.finite_singleton _).union (Set.finite_singleton _)).union
    (Set.finite_singleton _)).union (Set.finite_singleton _)

theorem S2696Vbad_odd (D : S2696FourPlaceData) :
    ∀ p, p ∈ S2696Vbad D →
      Odd (NumberFieldFinitePlace.residueCharacteristic p) := by
  intro p hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact D.odd5a
  · exact D.odd5b
  · exact D.odd2161a
  · exact D.odd2161b

noncomputable def S2696Selection (l : PrimeGeFive) (D : S2696FourPlaceData) :
    SourcePlaceSelection (S1280Arithmetic l) where
  V_mod_bad := S2696Vbad D
  V_mod_bad_odd_residue_characteristic := S2696Vbad_odd D
  V_mod_bad_nonempty := S2696Vbad_nonempty D

noncomputable def S2696BadQAbsLog (D : S2696FourPlaceData)
    (q : (p : NumberField.FinitePlace GaussianField) → p ∈ S2696Vbad D → Real) :
    Real := by
  classical
  letI : Fintype {p : NumberField.FinitePlace GaussianField // p ∈ S2696Vbad D} :=
    (S2696Vbad_finite D).fintype
  exact ∑ p : {p : NumberField.FinitePlace GaussianField // p ∈ S2696Vbad D},
    q p.1 p.2

#check S2696FourPlaceData
#check S2696Vbad
#check S2696Vbad_nonempty
#check S2696Vbad_finite
#check S2696Vbad_odd
#check S2696Selection
#check S2696BadQAbsLog

end LeanFormal.IUT.XiFPaper.S2696VbadActual
end
