import tmp.sheaf.xif.paper.S2697Two2161PlacesActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2697Two2161PlacesActual
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2698Two2161ResidueActual

local instance s2698Fact2161 : Fact (Nat.Prime 2161) := ⟨S2697Prime2161⟩

local instance s2698GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

noncomputable def S2698GaussianIntResidueMapPlus : GaussianInt →+* ZMod 2161 :=
  Zsqrtd.lift ⟨(2014 : ZMod 2161), by decide⟩

theorem S2698GaussianIntResidueMapPlus_generator :
    S2698GaussianIntResidueMapPlus S2697GaussianIntPlus = 0 := by
  simp [S2698GaussianIntResidueMapPlus, S2697GaussianIntPlus]
  decide

theorem S2698GaussianIntResidueMapPlus_surjective :
    Function.Surjective S2698GaussianIntResidueMapPlus := by
  intro y
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective y
  refine ⟨(a : GaussianInt), ?_⟩
  simp [S2698GaussianIntResidueMapPlus]

theorem S2698GaussianIntPlus_ideal_le_ker :
    Ideal.span {S2697GaussianIntPlus} ≤ RingHom.ker S2698GaussianIntResidueMapPlus := by
  refine Ideal.span_le.mpr ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (RingHom.mem_ker).mpr S2698GaussianIntResidueMapPlus_generator

theorem S2698GaussianIntResidueMapPlus_ker :
    RingHom.ker S2698GaussianIntResidueMapPlus =
      Ideal.span {S2697GaussianIntPlus} := by
  have hker : (RingHom.ker S2698GaussianIntResidueMapPlus).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective S2698GaussianIntResidueMapPlus
      S2698GaussianIntResidueMapPlus_surjective
  exact (Ideal.IsMaximal.eq_of_le S2697GaussianIntPlus_ideal_isMaximal hker.ne_top
    S2698GaussianIntPlus_ideal_le_ker).symm

noncomputable def S2698GaussianIntResidueEquivPlus :
    (GaussianInt ⧸ Ideal.span {S2697GaussianIntPlus}) ≃+* ZMod 2161 :=
  (Ideal.quotEquivOfEq S2698GaussianIntResidueMapPlus_ker.symm).trans
    (RingHom.quotientKerEquivOfSurjective S2698GaussianIntResidueMapPlus_surjective)

noncomputable def S2698FieldResidueEquivPlus :
    (gaussianRingOfIntegers ⧸ S2697GaussianFieldPrimePlus) ≃+* ZMod 2161 :=
  (Ideal.quotientEquiv S2697GaussianFieldPrimePlus
    (Ideal.span {S2697GaussianIntPlus})
    gaussianRingOfIntegersEquivGaussianInt
    (by
      change Ideal.span {S2697GaussianIntPlus} =
        Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom
          S2697GaussianFieldPrimePlus
      rw [S2697GaussianFieldPrimePlus,
        Ideal.map_comap_of_surjective
          gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianRingOfIntegersEquivGaussianInt.surjective])).trans
    S2698GaussianIntResidueEquivPlus

theorem S2698PlacePlus_maximalIdeal :
    S2697GaussianPlacePlus.maximalIdeal.asIdeal = S2697GaussianFieldPrimePlus :=
  congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
    (NumberField.FinitePlace.maximalIdeal_mk _)

theorem S2698ResidueCharacteristicPlus :
    NumberFieldFinitePlace.residueCharacteristic S2697GaussianPlacePlus = 2161 := by
  unfold NumberFieldFinitePlace.residueCharacteristic NumberFieldFinitePlace.ResidueField
  rw [S2698PlacePlus_maximalIdeal]
  let e := S2698FieldResidueEquivPlus
  have hzero : (2161 : gaussianRingOfIntegers ⧸ S2697GaussianFieldPrimePlus) = 0 := by
    apply e.injective
    rw [map_zero]
    change e ((2161 : ℕ) : gaussianRingOfIntegers ⧸ S2697GaussianFieldPrimePlus) = 0
    rw [map_natCast, ZMod.natCast_self]
  exact CharP.ringChar_of_prime_eq_zero S2697Prime2161 hzero

#print axioms S2698ResidueCharacteristicPlus
noncomputable def S2698GaussianIntResidueMapMinus : GaussianInt →+* ZMod 2161 :=
  Zsqrtd.lift ⟨(147 : ZMod 2161), by decide⟩

theorem S2698GaussianIntResidueMapMinus_generator :
    S2698GaussianIntResidueMapMinus S2697GaussianIntMinus = 0 := by
  simp [S2698GaussianIntResidueMapMinus, S2697GaussianIntMinus]
  decide

theorem S2698GaussianIntResidueMapMinus_surjective :
    Function.Surjective S2698GaussianIntResidueMapMinus := by
  intro y
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective y
  refine ⟨(a : GaussianInt), ?_⟩
  simp [S2698GaussianIntResidueMapMinus]

theorem S2698GaussianIntMinus_ideal_le_ker :
    Ideal.span {S2697GaussianIntMinus} ≤ RingHom.ker S2698GaussianIntResidueMapMinus := by
  refine Ideal.span_le.mpr ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (RingHom.mem_ker).mpr S2698GaussianIntResidueMapMinus_generator

theorem S2698GaussianIntResidueMapMinus_ker :
    RingHom.ker S2698GaussianIntResidueMapMinus =
      Ideal.span {S2697GaussianIntMinus} := by
  have hker : (RingHom.ker S2698GaussianIntResidueMapMinus).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective S2698GaussianIntResidueMapMinus
      S2698GaussianIntResidueMapMinus_surjective
  exact (Ideal.IsMaximal.eq_of_le S2697GaussianIntMinus_ideal_isMaximal hker.ne_top
    S2698GaussianIntMinus_ideal_le_ker).symm

noncomputable def S2698GaussianIntResidueEquivMinus :
    (GaussianInt ⧸ Ideal.span {S2697GaussianIntMinus}) ≃+* ZMod 2161 :=
  (Ideal.quotEquivOfEq S2698GaussianIntResidueMapMinus_ker.symm).trans
    (RingHom.quotientKerEquivOfSurjective S2698GaussianIntResidueMapMinus_surjective)

noncomputable def S2698FieldResidueEquivMinus :
    (gaussianRingOfIntegers ⧸ S2697GaussianFieldPrimeMinus) ≃+* ZMod 2161 :=
  (Ideal.quotientEquiv S2697GaussianFieldPrimeMinus
    (Ideal.span {S2697GaussianIntMinus})
    gaussianRingOfIntegersEquivGaussianInt
    (by
      change Ideal.span {S2697GaussianIntMinus} =
        Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom
          S2697GaussianFieldPrimeMinus
      rw [S2697GaussianFieldPrimeMinus,
        Ideal.map_comap_of_surjective
          gaussianRingOfIntegersEquivGaussianInt.toRingHom
          gaussianRingOfIntegersEquivGaussianInt.surjective])).trans
    S2698GaussianIntResidueEquivMinus

theorem S2698PlaceMinus_maximalIdeal :
    S2697GaussianPlaceMinus.maximalIdeal.asIdeal = S2697GaussianFieldPrimeMinus :=
  congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
    (NumberField.FinitePlace.maximalIdeal_mk _)

theorem S2698ResidueCharacteristicMinus :
    NumberFieldFinitePlace.residueCharacteristic S2697GaussianPlaceMinus = 2161 := by
  unfold NumberFieldFinitePlace.residueCharacteristic NumberFieldFinitePlace.ResidueField
  rw [S2698PlaceMinus_maximalIdeal]
  let e := S2698FieldResidueEquivMinus
  have hzero : (2161 : gaussianRingOfIntegers ⧸ S2697GaussianFieldPrimeMinus) = 0 := by
    apply e.injective
    rw [map_zero]
    change e ((2161 : ℕ) : gaussianRingOfIntegers ⧸ S2697GaussianFieldPrimeMinus) = 0
    rw [map_natCast, ZMod.natCast_self]
  exact CharP.ringChar_of_prime_eq_zero S2697Prime2161 hzero

theorem S2698ResidueCharacteristic2161 :
    NumberFieldFinitePlace.residueCharacteristic S2697GaussianPlacePlus = 2161 ∧
    NumberFieldFinitePlace.residueCharacteristic S2697GaussianPlaceMinus = 2161 :=
  ⟨S2698ResidueCharacteristicPlus, S2698ResidueCharacteristicMinus⟩

theorem S2698OddPlus :
    Odd (NumberFieldFinitePlace.residueCharacteristic S2697GaussianPlacePlus) := by
  rw [S2698ResidueCharacteristicPlus]
  norm_num

theorem S2698OddMinus :
    Odd (NumberFieldFinitePlace.residueCharacteristic S2697GaussianPlaceMinus) := by
  rw [S2698ResidueCharacteristicMinus]
  norm_num

#print axioms S2698ResidueCharacteristic2161
#print axioms S2698OddPlus
#print axioms S2698OddMinus

end LeanFormal.IUT.XiFPaper.S2698Two2161ResidueActual
end
