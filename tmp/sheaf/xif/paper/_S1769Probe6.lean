import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1769Probe

variable {K : Type} [Field K]

abbrev bc (K : Type) [Field K] : CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} (AlgebraicClosure K) :=
  CommAlgCat.FiniteEtale.baseChange K (AlgebraicClosure K)

theorem bc_reflectsIsos : (bc K).ReflectsIsomorphisms where
  reflects {A B} f hf := by
    haveI : IsIso ((bc K).map f).hom := (ObjectProperty.isIso_hom_iff ((bc K).map f)).mpr hf
    have hbij : Function.Bijective (((bc K).map f).hom.hom) := by
      exact (ConcreteCategory.isIso_iff_bijective ((bc K).map f).hom).mp inferInstance
    have hfun : (fun x => ((bc K).map f).hom.hom x) =
        (fun x => LinearMap.lTensor (AlgebraicClosure K) f.hom.hom.toLinearMap x) := by
      funext x
      rfl
    have hbij' : Function.Bijective (fun x => LinearMap.lTensor (AlgebraicClosure K) f.hom.hom.toLinearMap x) := by
      simpa only [hfun] using hbij
    have hf' : Function.Bijective f.hom.hom.toLinearMap := by
      exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective (R := K) (M := AlgebraicClosure K) (f := f.hom.hom.toLinearMap)).mp hbij'
    have hf'' : Function.Bijective f.hom.hom := hf'
    haveI : IsIso f.hom := (ConcreteCategory.isIso_iff_bijective f.hom).mpr hf''
    exact (ObjectProperty.isIso_hom_iff f).mp inferInstance

end S1769Probe