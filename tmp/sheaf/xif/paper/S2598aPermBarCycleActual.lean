import tmp.sheaf.xif.paper.S2588FbarIrreducibleActual
import tmp.sheaf.xif.paper.S2599TInstancesActual
import tmp.sheaf.xif.paper.S2596rLiftTLAuxActual
import tmp.sheaf.xif.paper.S2596zTPrimeBatch1Actual
import tmp.sheaf.xif.paper.S2536LocalizedPowersActual
import tmp.sheaf.xif.paper.S2539AbstractRedRootActual
import tmp.sheaf.xif.paper.S2540AbstractPermBarActual
import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
import tmp.sheaf.xif.paper.S2547NormalizeActual
import tmp.sheaf.xif.paper.S2592GenericLocalizedResidueIsoActual
import tmp.sheaf.xif.paper.S2003Psi5ModelActual
import tmp.sheaf.xif.paper.S1942PrePsiFiveActual
import tmp.sheaf.xif.paper.S2309SubfieldUniqueActual
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2598aPermBarCycleActual

abbrev C0 : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.C
abbrev K0 : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.L
abbrev L0 : Type := LeanFormal.IUT.XiFPaper.S2599TInstancesActual.L
abbrev OL0 : Type := NumberField.RingOfIntegers L0
abbrev S0 : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.S
abbrev T0 : Type := LeanFormal.IUT.XiFPaper.S2599TInstancesActual.T

abbrev cden : C0 := (LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Cden : ℤ)

abbrev MS : Submonoid C0 := Submonoid.powers cden

lemma cden_ne_zero : cden ≠ 0 := Int.cast_ne_zero.mpr
  LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Cden_ne_zero

lemma cden_mem_nzd : cden ∈ nonZeroDivisors C0 := mem_nonZeroDivisors_of_ne_zero cden_ne_zero

lemma map_cden_ne_zero : algebraMap C0 OL0 cden ≠ 0 := by
  simpa using (FaithfulSMul.algebraMap_injective C0 OL0).ne cden_ne_zero

lemma hM_le_nzd : Submonoid.powers (algebraMap C0 OL0 cden) ≤ nonZeroDivisors OL0 := by
  rw [Submonoid.powers_le]
  exact mem_nonZeroDivisors_of_ne_zero map_cden_ne_zero

noncomputable instance instIsDomainT0 : IsDomain T0 :=
  IsLocalization.isDomain_of_le_nonZeroDivisors
    (M := Submonoid.powers (algebraMap C0 OL0 cden)) (S := T0) hM_le_nzd

noncomputable instance instIsFractionRingS0 : IsFractionRing S0 K0 :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (R := C0) (M := MS) (S := S0) (T := K0)

noncomputable instance instIsDomainS0 : IsDomain S0 :=
  (IsFractionRing.injective S0 K0).isDomain

noncomputable instance instFaithfulSMulS0K0 : FaithfulSMul S0 K0 :=
  (faithfulSMul_iff_algebraMap_injective S0 K0).mpr (IsFractionRing.injective S0 K0)

lemma algebraMapSubmonoid_eq_powers :
    Algebra.algebraMapSubmonoid OL0 MS
      = Submonoid.powers (algebraMap C0 OL0 cden) := by
  rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]

noncomputable instance instIsLocOL0T0 : IsLocalization (Algebra.algebraMapSubmonoid OL0 MS) T0 := by
  rw [algebraMapSubmonoid_eq_powers]
  exact inferInstance

lemma isScalarTower_OL0_T0_L0 : IsScalarTower OL0 T0 L0 := by
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  show algebraMap OL0 L0 x = algebraMap T0 L0 (algebraMap OL0 T0 x)
  rw [show algebraMap T0 L0 (algebraMap OL0 T0 x)
      = LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gOL x from
    DFunLike.congr_fun (IsLocalization.lift_comp
      (M := Submonoid.powers (algebraMap C0 OL0 cden))
      (g := LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gOL)
      (fun y => LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gOL_unit y.1 y.2)) x]
  rfl

abbrev cZ : ℤ := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.c

abbrev MZ : Submonoid C0 := Algebra.algebraMapSubmonoid C0 (Submonoid.powers cZ)

lemma algebraMap_C0_OL0_L0 (x : C0) :
    algebraMap OL0 L0 (algebraMap C0 OL0 x) = algebraMap C0 L0 x := by
  rw [IsScalarTower.algebraMap_apply C0 K0 L0]
  have h1 : algebraMap OL0 L0 (algebraMap C0 OL0 x) = algebraMap K0 L0 (x : K0) := by
    have h2 : ((algebraMap C0 OL0 x : OL0) : L0) = algebraMap K0 L0 (x : K0) := by
      change ((NumberField.RingOfIntegers.mapRingHom (algebraMap K0 L0)) x : L0) = _
      exact NumberField.RingOfIntegers.mapRingHom_apply _ x
    rwa [NumberField.RingOfIntegers.coe_eq_algebraMap] at h2
  rw [h1]

lemma isScalarTower_C0_OL0_L0 : IsScalarTower C0 OL0 L0 := by
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  exact (algebraMap_C0_OL0_L0 x).symm

lemma algebraMap_C0_S0_L0 (x : C0) :
    algebraMap S0 L0 (algebraMap C0 S0 x) = algebraMap C0 L0 x := by
  rw [IsScalarTower.algebraMap_apply S0 K0 L0]
  rw [← IsScalarTower.algebraMap_apply C0 S0 K0]
  rw [← IsScalarTower.algebraMap_apply C0 K0 L0]

lemma isScalarTower_C0_S0_L0 : IsScalarTower C0 S0 L0 := by
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  exact (algebraMap_C0_S0_L0 x).symm

lemma liftST_comp_algebraMap :
    (LeanFormal.IUT.XiFPaper.S2599TInstancesActual.liftST.comp (algebraMap C0 S0))
      = (algebraMap OL0 T0).comp (algebraMap C0 OL0) :=
  IsLocalization.lift_comp
    (M := MZ)
    (g := LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gCT)
    (fun y => LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gCT_unit y.1 y.2)

lemma isScalarTower_C0_S0_T0 : IsScalarTower C0 S0 T0 := by
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  show algebraMap C0 T0 x = algebraMap S0 T0 (algebraMap C0 S0 x)
  rw [show (algebraMap C0 T0) = (algebraMap OL0 T0).comp (algebraMap C0 OL0) from rfl]
  rw [show algebraMap S0 T0 (algebraMap C0 S0 x)
      = LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gCT x from
    DFunLike.congr_fun liftST_comp_algebraMap x]
  rfl

lemma liftTL_comp_algebraMap :
    (LeanFormal.IUT.XiFPaper.S2599TInstancesActual.liftTL.comp (algebraMap OL0 T0))
      = (algebraMap OL0 L0) :=
  IsLocalization.lift_comp
    (M := Submonoid.powers (algebraMap C0 OL0 cden))
    (g := LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gOL)
    (fun y => LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gOL_unit y.1 y.2)

lemma algebraMap_S0_L0_eq : (algebraMap S0 L0) = (algebraMap T0 L0).comp (algebraMap S0 T0) := by
  refine IsLocalization.ringHom_ext (M := MZ) ?_
  ext x
  simp only [RingHom.comp_apply]
  rw [algebraMap_C0_S0_L0 x]
  have hST : algebraMap S0 T0 (algebraMap C0 S0 x)
      = LeanFormal.IUT.XiFPaper.S2599TInstancesActual.liftST (algebraMap C0 S0 x) := rfl
  rw [hST]
  have h1 : LeanFormal.IUT.XiFPaper.S2599TInstancesActual.liftST (algebraMap C0 S0 x)
      = LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gCT x :=
    DFunLike.congr_fun liftST_comp_algebraMap x
  rw [h1]
  have h2 : LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gCT x
      = algebraMap OL0 T0 (algebraMap C0 OL0 x) := rfl
  rw [h2]
  have h3 : algebraMap T0 L0 (algebraMap OL0 T0 (algebraMap C0 OL0 x))
      = LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gOL (algebraMap C0 OL0 x) :=
    DFunLike.congr_fun liftTL_comp_algebraMap (algebraMap C0 OL0 x)
  rw [h3]
  have h4 : LeanFormal.IUT.XiFPaper.S2599TInstancesActual.gOL (algebraMap C0 OL0 x)
      = algebraMap OL0 L0 (algebraMap C0 OL0 x) := rfl
  rw [h4]
  rw [algebraMap_C0_OL0_L0 x]

lemma isScalarTower_S0_T0_L0 : IsScalarTower S0 T0 L0 :=
  IsScalarTower.of_algebraMap_eq' algebraMap_S0_L0_eq

noncomputable instance instIsIntegralClosureT0 : IsIntegralClosure T0 S0 L0 :=
  LeanFormal.IUT.XiFPaper.S2536LocalizedPowersActual.isIntegralClosure_localization_powers
    (A := C0) (C := OL0) (K := K0) (L := L0) (R := S0) (S := T0)
    (a := cden) cden_mem_nzd
    isScalarTower_C0_OL0_L0 isScalarTower_C0_S0_T0 (by infer_instance)
    isScalarTower_C0_S0_L0 isScalarTower_OL0_T0_L0 isScalarTower_S0_T0_L0

lemma algebraMap_S0_T0_injective : Function.Injective (algebraMap S0 T0) := by
  intro x y h
  have h2 : algebraMap S0 L0 x = algebraMap S0 L0 y := by
    rw [algebraMap_S0_L0_eq]
    simp only [RingHom.comp_apply]
    rw [h]
  rw [IsScalarTower.algebraMap_apply S0 K0 L0, IsScalarTower.algebraMap_apply S0 K0 L0] at h2
  exact IsFractionRing.injective S0 K0 ((FaithfulSMul.algebraMap_injective K0 L0) h2)

instance instAlgebraIsIntegralT0 : Algebra.IsIntegral S0 T0 := by
  haveI : IsScalarTower S0 T0 L0 := isScalarTower_S0_T0_L0
  constructor
  intro x
  have h : IsIntegral S0 (algebraMap T0 L0 x) :=
    IsIntegralClosure.isIntegral_iff.mpr ⟨x, rfl⟩
  exact (isIntegral_algebraMap_iff (IsIntegralClosure.algebraMap_injective T0 S0 L0)).mp h

abbrev Wit : Type := LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual.S2584PrimeDegreeOneWitness

lemma ker_algebraMap_S0_T0_le (W : Wit) : RingHom.ker (algebraMap S0 T0) ≤ W.P := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  have h0 : x = 0 := algebraMap_S0_T0_injective (by rw [hx, map_zero])
  rw [h0]
  exact W.P.zero_mem

noncomputable instance instMaximalP (W : Wit) : W.P.IsMaximal :=
  LeanFormal.IUT.XiFPaper.S2586PrimeMaximalActual.S2586_P_isMaximal W

noncomputable def Pbar (W : Wit) : Ideal T0 :=
  Classical.choose (Ideal.exists_ideal_over_maximal_of_isIntegral (R := S0) (S := T0) W.P
    (ker_algebraMap_S0_T0_le W))

lemma Pbar_spec (W : Wit) :
    (Pbar W).IsMaximal ∧ (Pbar W).comap (algebraMap S0 T0) = W.P :=
  Classical.choose_spec (Ideal.exists_ideal_over_maximal_of_isIntegral
    (R := S0) (S := T0) W.P (ker_algebraMap_S0_T0_le W))

lemma Pbar_isMaximal (W : Wit) : (Pbar W).IsMaximal := (Pbar_spec W).1

noncomputable instance instFintypeS0Quot (W : Wit) : Fintype (S0 ⧸ W.P) :=
  Fintype.ofEquiv (ZMod 613) W.residueEquivS.symm

abbrev fbarW (W : Wit) : (S0 ⧸ W.P)[X] :=
  LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual.fbar
    LeanFormal.IUT.XiFPaper.S2574LocalizedP12Actual.S2574f W.P

lemma fbarW_monic (W : Wit) : (fbarW W).Monic :=
  Polynomial.Monic.map (Ideal.Quotient.mk W.P)
    LeanFormal.IUT.XiFPaper.S2574LocalizedP12Actual.S2574f_monic

lemma fbarW_irreducible (W : Wit) : Irreducible (fbarW W) :=
  LeanFormal.IUT.XiFPaper.S2588FbarIrreducibleActual.S2587FbarIrreducibleRequired_holds W

lemma fbarW_natDegree (W : Wit) : (fbarW W).natDegree = 12 :=
  LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual.fbar_natDegree W

noncomputable instance instFieldS0Quot (W : Wit) : Field (S0 ⧸ W.P) :=
  Ideal.Quotient.field W.P

noncomputable instance instFiniteS0Quot (W : Wit) : Finite (S0 ⧸ W.P) :=
  Finite.of_fintype _

instance instST_S0_T0_L0 : IsScalarTower S0 T0 L0 := isScalarTower_S0_T0_L0

noncomputable instance instDecEqS0Quot (W : Wit) : DecidableEq (S0 ⧸ W.P) :=
  Classical.decEq _

noncomputable instance instDecEqT0Quot (P : Ideal T0) : DecidableEq (T0 ⧸ P) :=
  Classical.decEq _

theorem S2598a_permBar_cycleType_12
    (W : Wit) (P : Ideal T0) [hP : P.IsPrime] [hPover : P.LiesOver W.P] [hPmax : P.IsMaximal]
    [Fintype (T0 ⧸ P)]
    (hcard : Fintype.card ((fbarW W).rootSet (T0 ⧸ P)) = 12)
    (htrans : ∀ x y : (fbarW W).rootSet (T0 ⧸ P),
      ∃ n : ℕ,
        ((LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual.permBar
          (f := LeanFormal.IUT.XiFPaper.S2574LocalizedP12Actual.S2574f)
          (p := W.P) (P := P))^n) x = y) :
    (LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual.permBar
        (f := LeanFormal.IUT.XiFPaper.S2574LocalizedP12Actual.S2574f)
        (p := W.P) (P := P)).cycleType = ({12} : Multiset ℕ) := by
  classical
  set sigma := LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual.permBar
    (f := LeanFormal.IUT.XiFPaper.S2574LocalizedP12Actual.S2574f) (p := W.P) (P := P)
  haveI hnt : Nontrivial ((fbarW W).rootSet (T0 ⧸ P)) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hcycleOn : sigma.IsCycleOn (Set.univ : Set ((fbarW W).rootSet (T0 ⧸ P))) := by
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · exact fun x _ => Set.mem_univ _
      · exact fun x _ y _ h => sigma.injective h
      · intro y _
        exact ⟨sigma.symm y, Set.mem_univ _, sigma.apply_symm_apply y⟩
    · intro x _ y _
      obtain ⟨n, hn⟩ := htrans x y
      exact ⟨(n : ℤ), by rwa [zpow_natCast]⟩
  have hsupport : sigma.support = Finset.univ := by
    ext y
    rw [Equiv.Perm.mem_support]
    simp only [Finset.mem_univ, iff_true]
    exact hcycleOn.apply_ne Set.nontrivial_univ (Set.mem_univ y)
  have hcycle : sigma.IsCycle := by
    rw [Equiv.Perm.isCycle_iff_exists_isCycleOn]
    exact ⟨Set.univ, Set.nontrivial_univ, hcycleOn, fun x _ => Set.mem_univ x⟩
  rw [hcycle.cycleType, hsupport, Finset.card_univ, hcard]

#print axioms S2598a_permBar_cycleType_12

end LeanFormal.IUT.XiFPaper.S2598aPermBarCycleActual
end
