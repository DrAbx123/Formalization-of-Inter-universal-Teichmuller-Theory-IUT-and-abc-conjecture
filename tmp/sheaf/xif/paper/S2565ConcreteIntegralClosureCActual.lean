import Mathlib.RingTheory.Localization.Basic
import Mathlib.NumberTheory.NumberField.Basic
import tmp.sheaf.xif.paper.S2536LocalizedPowersActual
import tmp.sheaf.xif.paper.S2562HZcMonicCActual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
noncomputable section
set_option maxHeartbeats 16000000
open NumberField
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
namespace LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
noncomputable def c : ℤ := LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Cden
abbrev A : Type := ℤ
abbrev C : Type := RingOfIntegers S1720Field
abbrev K : Type := ℚ
abbrev L : Type := S1720Field
abbrev M : Submonoid A := Submonoid.powers c
abbrev R : Type := Localization M
abbrev S : Type := Localization (Algebra.algebraMapSubmonoid C M)
theorem hAL_inj : Function.Injective (algebraMap A L) := by
  intro x y h
  exact_mod_cast h
theorem hcA : (c : A) ≠ 0 := by
  exact LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Cden_ne_zero
theorem hcL_ne : algebraMap A L (c : A) ≠ 0 := by
  simpa using hAL_inj.ne hcA
theorem hcC_ne : algebraMap C L (c : C) ≠ 0 := by
  have hmap : algebraMap C L (c : C) = algebraMap A L (c : A) := by
    rw [IsScalarTower.algebraMap_apply A C L]
    norm_num
  rw [hmap]
  exact hcL_ne
theorem hc_mem : (c : A) ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero hcA
noncomputable def liftAL : R →+* L :=
  IsLocalization.lift (M := M) (g := algebraMap A L)
    (by
      intro m
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (m : A) (c : A)).mp m.2
      rw [← hn, map_pow]
      exact IsUnit.pow n (isUnit_iff_ne_zero.mpr hcL_ne))
noncomputable instance : Algebra R L := liftAL.toAlgebra
lemma liftAL_comp : liftAL.comp (algebraMap A R) = algebraMap A L :=
  IsLocalization.lift_comp _
noncomputable def liftCL : S →+* L :=
  IsLocalization.lift (M := Algebra.algebraMapSubmonoid C M) (g := algebraMap C L)
    (by
      intro m
      obtain ⟨a, ha, hm⟩ := m.2
      rw [← hm]
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff a (c : A)).mp ha
      rw [← hn]
      simp only [map_pow, IsScalarTower.algebraMap_apply A C L]
      exact IsUnit.pow n (isUnit_iff_ne_zero.mpr hcL_ne))
noncomputable instance : Algebra S L := liftCL.toAlgebra
lemma liftCL_comp : liftCL.comp (algebraMap C S) = algebraMap C L :=
  IsLocalization.lift_comp _
noncomputable def liftRS_hy :
    M ≤ (Algebra.algebraMapSubmonoid C M).comap (algebraMap A C) :=
  M.le_comap_map

noncomputable def liftRS : R →+* S :=
  IsLocalization.map S (algebraMap A C) liftRS_hy
noncomputable instance : Algebra R S := liftRS.toAlgebra
lemma liftRS_comp :
    liftRS.comp (algebraMap A R) = (algebraMap C S).comp (algebraMap A C) := by
  haveI : IsLocalization (Submonoid.map (algebraMap A C) M) S :=
    (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid C M) S)
  exact IsLocalization.map_comp (M := M) (S := R) (Q := S)
    (g := algebraMap A C) (hy := liftRS_hy)
noncomputable instance : Algebra A S :=
  (((algebraMap C S).comp (algebraMap A C))).toAlgebra
local instance : SMul A R := Algebra.toSMul
local instance : SMul R S := Algebra.toSMul
local instance : SMul A S := Algebra.toSMul
local instance : SMul A C := Algebra.toSMul
local instance : SMul C S := Algebra.toSMul
local instance : SMul A L := Algebra.toSMul
local instance : SMul C L := Algebra.toSMul
local instance : SMul R L := Algebra.toSMul
local instance : SMul S L := Algebra.toSMul

noncomputable instance : IsScalarTower A R L := by
  apply IsScalarTower.of_algebraMap_eq'
  ext a
  exact (DFunLike.congr_fun liftAL_comp a).symm
noncomputable instance : IsScalarTower C S L := by
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  exact (DFunLike.congr_fun liftCL_comp c).symm
noncomputable instance : IsScalarTower A R S := by
  apply IsScalarTower.of_algebraMap_eq'
  ext a
  exact (DFunLike.congr_fun liftRS_comp a).symm
noncomputable instance : IsScalarTower A C S := by
  apply IsScalarTower.of_algebraMap_eq'
  ext a; rfl
lemma liftRS_liftCL : liftCL.comp liftRS = liftAL := by
  apply IsLocalization.ringHom_ext M
  rw [RingHom.comp_assoc, liftRS_comp, ← RingHom.comp_assoc, liftCL_comp,
    liftAL_comp]
  exact (IsScalarTower.algebraMap_eq A C L).symm
noncomputable instance : IsScalarTower R S L := by
  apply IsScalarTower.of_algebraMap_eq'
  ext r
  exact (DFunLike.congr_fun liftRS_liftCL r).symm
noncomputable instance hACL_inst : IsScalarTower A C L :=
  IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (IsScalarTower.algebraMap_apply A C L a).symm)
theorem S2555_isIntegralClosure : IsIntegralClosure S R L := by
  haveI hAK : IsFractionRing A K := IsIntegralClosure.isFractionRing_of_finite_extension ℤ ℚ K A
  haveI hCL : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  exact LeanFormal.IUT.XiFPaper.S2536LocalizedPowersActual.isIntegralClosure_localization_powers
    (A := A) (C := C) (K := K) (L := L) (R := R) (S := S)
    (a := (c : A)) hc_mem
    (hACL := hACL_inst) (hARS := inferInstance) (hACS := inferInstance)
    (hARL := inferInstance) (hCSL := inferInstance) (hRSL := inferInstance)
#print axioms S2555_isIntegralClosure
end LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
end
