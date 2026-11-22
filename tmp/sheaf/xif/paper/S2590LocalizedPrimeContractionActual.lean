import tmp.sheaf.xif.paper.S2587LocalizedResidueDataActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S2590LocalizedPrimeContractionActual

open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual

abbrev C : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.C
abbrev S : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.S

theorem S2590_contraction_maximal
    (D : S2587LocalizedResidueDataS)
    (h613 : algebraMap ℤ S (613 : ℤ) ∈ D.p) :
    (D.p.comap (algebraMap C S)).IsMaximal := by
  haveI hpmax : D.p.IsPrime := D.p_max.isPrime
  haveI hprime : (D.p.comap (algebraMap C S)).IsPrime := Ideal.comap_isPrime _ _
  have hne : D.p.comap (algebraMap C S) ≠ ⊥ := by
    intro hbot
    have hmem : (613 : C) ∈ D.p.comap (algebraMap C S) := by
      rw [Ideal.mem_comap]
      have hcomm : algebraMap C S (613 : C) = algebraMap ℤ S (613 : ℤ) := by
        change algebraMap C S (algebraMap ℤ C (613 : ℤ)) = algebraMap ℤ S (613 : ℤ)
        rw [IsScalarTower.algebraMap_apply ℤ C S]
      rw [hcomm]
      exact h613
    rw [hbot] at hmem
    have h613C : (613 : C) ≠ 0 := by norm_num
    exact h613C (by simpa using hmem)
  exact Ideal.IsPrime.isMaximal hprime hne

#print axioms S2590_contraction_maximal

end LeanFormal.IUT.XiFPaper.S2590LocalizedPrimeContractionActual
end
