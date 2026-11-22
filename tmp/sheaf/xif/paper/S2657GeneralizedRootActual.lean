import tmp.sheaf.xif.paper.S2655NonmonicRangeActual
import tmp.sheaf.xif.paper.S2440RangePairTransitiveSubagentActual

noncomputable section
set_option maxHeartbeats 4000000

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2655NonmonicRangeActual
open LeanFormal.IUT.XiFPaper.S2653DedekindToRangeActual
open LeanFormal.IUT.XiFPaper.S2643RootTransportFixActual
open LeanFormal.IUT.XiFPaper.S2642RootToRangeTransport
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual

namespace LeanFormal.IUT.XiFPaper.S2657GeneralizedRootActual

noncomputable def S2657RootPerm
    (f : S1720Field[X])
    (hsplit : (f.map (algebraMap S1720Field
      S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field)) :
    Equiv.Perm (f.rootSet S2057FiveDivisionField) := by
  let p : S1720Field[X] := f
  have h : (p.map (algebraMap S1720Field S2057FiveDivisionField)).Splits := by
    simpa [p] using hsplit
  letI : Fact ((p.map (algebraMap S1720Field
    S2057FiveDivisionField)).Splits) := ⟨h⟩
  exact MulAction.toPermHom (Gal(S2057FiveDivisionField/S1720Field))
    (p.rootSet S2057FiveDivisionField) σ

theorem S2657RootPerm_apply_val
    (f : S1720Field[X])
    (hsplit : (f.map (algebraMap S1720Field
      S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field))
    (x : f.rootSet S2057FiveDivisionField) :
    (S2657RootPerm f hsplit σ x).1 = σ x.1 := by
  simp only [S2657RootPerm, MulAction.toPermHom_apply, MulAction.toPerm_apply,
    Polynomial.rootSet.coe_smul, AlgEquiv.smul_def]

theorem S2657PairCongr
    (f : S1720Field[X])
    (hsplit : (f.map (algebraMap S1720Field
      S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field))
    {c : S1720Field} (hc : c ≠ 0)
    (hq : f = C c * S2057Psi5F) :
    (S2653rootSetEquiv (K := S1720Field)
      (A := S2057FiveDivisionField) hc hq).permCongr
        (S2657RootPerm f hsplit σ) =
      S2132DivisionRootEquiv σ := by
  classical
  ext x
  rw [Equiv.permCongr_apply]
  change (S2657RootPerm f hsplit σ
    ((S2653rootSetEquiv (K := S1720Field)
      (A := S2057FiveDivisionField) hc hq).symm x)).1 =
    (S2132DivisionRootEquiv σ x).1
  rw [S2657RootPerm_apply_val]
  rfl

theorem S2657CycleType_eq_divisionRootEquiv
    (f : S1720Field[X])
    (hsplit : (f.map (algebraMap S1720Field
      S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field))
    {c : S1720Field} (hc : c ≠ 0)
    (hq : f = C c * S2057Psi5F) :
    (S2657RootPerm f hsplit σ).cycleType =
      Equiv.Perm.cycleType (S2132DivisionRootEquiv σ) := by
  classical
  rw [← S2657PairCongr f hsplit σ hc hq]
  rw [S2132cycleType_permCongr]

theorem S2657RangeTransport102
    (f : S1720Field[X])
    (hsplit : (f.map (algebraMap S1720Field
      S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field))
    {c : S1720Field} (hc : c ≠ 0)
    (hq : f = C c * S2057Psi5F)
    (hcyc : (S2657RootPerm f hsplit σ).cycleType =
      ({10, 2} : Multiset ℕ)) :
    S2203RangeCycleTypeRequired S1982Basis := by
  classical
  have hdiv : Equiv.Perm.cycleType (S2132DivisionRootEquiv σ) =
      ({10, 2} : Multiset ℕ) :=
    (S2657CycleType_eq_divisionRootEquiv f hsplit σ hc hq).symm.trans hcyc
  obtain ⟨σ', hσ'⟩ := S2502cycleType_transport σ
  refine S2642RootMapToRangeTransport σ' ?_
  rw [← S2653S2480RootPerm_eq_S2642RootPerm σ', hσ', hdiv]

theorem S2657PairTransitiveOfTwelveCycle
    (f : S1720Field[X])
    (hsplit : (f.map (algebraMap S1720Field
      S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field))
    {c : S1720Field} (hc : c ≠ 0)
    (hq : f = C c * S2057Psi5F)
    (hcyc : (S2657RootPerm f hsplit σ).cycleType =
      ({12} : Multiset ℕ)) :
    S2203RangePairTransitiveRequired S1982Basis := by
  classical
  have hdiv : Equiv.Perm.cycleType (S2132DivisionRootEquiv σ) =
      ({12} : Multiset ℕ) :=
    (S2657CycleType_eq_divisionRootEquiv f hsplit σ hc hq).symm.trans hcyc
  obtain ⟨σ', hσ'⟩ := S2502cycleType_transport σ
  have hroot : (S2642RootPerm σ').cycleType =
      ({12} : Multiset ℕ) := by
    rw [← S2653S2480RootPerm_eq_S2642RootPerm σ', hσ', hdiv]
  have hpair : (S2642PairPerm σ').cycleType =
      ({12} : Multiset ℕ) := by
    rw [S2642PairPerm_cycleType_eq_rootPerm σ', hroot]
  refine S2440RangePairTransitive_of_twelveCycle
    ⟨S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ',
      ?_, ?_⟩
  · exact MonoidHom.mem_range.mpr ⟨σ', rfl⟩
  · rw [S2642PairMatrix_cycleType σ']
    exact hpair

/-- Localized model: f over any R-algebra to F', using the field roots in L. -/
noncomputable def S2657LocalizedRootPerm
    (R : Type) [CommRing R] [Algebra R S1720Field]
    (f : R[X])
    (hsplit : (f.map (algebraMap R S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field)) :
    Equiv.Perm ((f.map (algebraMap R S1720Field)).rootSet
      S2057FiveDivisionField) :=
  S2657RootPerm (f.map (algebraMap R S1720Field)) (by
    rw [Polynomial.map_map]
    convert hsplit using 2
    exact IsScalarTower.algebraMap_eq R S1720Field
      S2057FiveDivisionField) σ

#check S2657PairTransitiveOfTwelveCycle
#check S2657LocalizedRootPerm
#print axioms S2657PairTransitiveOfTwelveCycle

#check S2657RootPerm
#check S2657CycleType_eq_divisionRootEquiv
#check S2657RangeTransport102
#print axioms S2657RangeTransport102

end LeanFormal.IUT.XiFPaper.S2657GeneralizedRootActual
end
