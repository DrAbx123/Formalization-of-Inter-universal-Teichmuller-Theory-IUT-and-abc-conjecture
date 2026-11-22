import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.AbsoluteGaloisGroup

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1769

abbrev C (K : Type) [Field K] : Type 1 := (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ

abbrev F (K : Type) [Field K] : C K ⥤ FintypeCat.{0} :=
  CommAlgCat.FiniteEtale.fiber K (AlgebraicClosure K)

abbrev bc (K : Type) [Field K] :
    CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} (AlgebraicClosure K) :=
  CommAlgCat.FiniteEtale.baseChange K (AlgebraicClosure K)

abbrev E (K : Type) [Field K] :
    (CommAlgCat.FiniteEtale.{0} (AlgebraicClosure K))ᵒᵖ ⥤ FintypeCat.{0} :=
  CommAlgCat.FiniteEtale.fiber (AlgebraicClosure K) (AlgebraicClosure K)

def fiberIso (K : Type) [Field K] : F K ≅ (bc K).op ⋙ E K :=
  CommAlgCat.FiniteEtale.fiberIsoBaseChangeFiber
    (R := K) (Ω := AlgebraicClosure K) (S := AlgebraicClosure K)

-- Field 1: terminal objects
instance selfInitial (K : Type) [Field K] (X : CommAlgCat.FiniteEtale.{0} K) :
    Unique (CommAlgCat.FiniteEtale.of K K ⟶ X) where
  default := CommAlgCat.FiniteEtale.ofHom (Algebra.ofId K X.obj)
  uniq f := by
    apply InducedCategory.hom_ext
    ext

def selfInitialObj (K : Type) [Field K] : IsInitial (CommAlgCat.FiniteEtale.of K K) :=
  IsInitial.ofUnique _

def selfTerminal (K : Type) [Field K] :
    IsTerminal (Opposite.op (CommAlgCat.FiniteEtale.of K K)) :=
  (selfInitialObj K).op

theorem terminal_iso_self (K : Type) [Field K] [PreGaloisCategory (C K)] :
    (⊤_ (C K)) ≅ Opposite.op (CommAlgCat.FiniteEtale.of K K) :=
  terminalIsTerminal.uniqueUpToIso (selfTerminal K)

theorem terminal_obj_subsingleton (K : Type) [Field K] [PreGaloisCategory (C K)] :
    Subsingleton ((F K).obj (⊤_ (C K)) : Type) := by
  let e := (F K).mapIso (terminal_iso_self K)
  let ee : ((F K).obj (⊤_ (C K)) : Type) ≃
      ((F K).obj (Opposite.op (CommAlgCat.FiniteEtale.of K K)) : Type) :=
    FintypeCat.equivEquivIso.symm e
  haveI : Subsingleton ((F K).obj (Opposite.op (CommAlgCat.FiniteEtale.of K K)) : Type) := by
    change Subsingleton ((CommAlgCat.FiniteEtale.of K K).obj →ₐ[K] AlgebraicClosure K)
    infer_instance
  refine ⟨fun x y => ?_⟩
  apply ee.injective
  exact Subsingleton.elim _ _

theorem terminal_obj_nonempty (K : Type) [Field K] [PreGaloisCategory (C K)] :
    Nonempty ((F K).obj (⊤_ (C K)) : Type) := by
  let e := (F K).mapIso (terminal_iso_self K)
  let ee : ((F K).obj (⊤_ (C K)) : Type) ≃
      ((F K).obj (Opposite.op (CommAlgCat.FiniteEtale.of K K)) : Type) :=
    FintypeCat.equivEquivIso.symm e
  exact ⟨ee.symm (Algebra.ofId K (AlgebraicClosure K))⟩

def terminal_obj_isTerminal (K : Type) [Field K] [PreGaloisCategory (C K)] :
    IsTerminal ((F K).obj (⊤_ (C K))) := by
  haveI : Subsingleton ((F K).obj (⊤_ (C K)) : Type) := terminal_obj_subsingleton K
  haveI : Nonempty ((F K).obj (⊤_ (C K)) : Type) := terminal_obj_nonempty K
  refine IsTerminal.ofUniqueHom (fun Y => FintypeCat.homMk (fun _ => Classical.arbitrary _)) ?_
  intro Y m
  apply FintypeCat.hom_ext
  intro y
  exact Subsingleton.elim _ _

theorem preservesTerminalObjects (K : Type) [Field K] [PreGaloisCategory (C K)] :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (F K) := by
  have h : PreservesLimit (Functor.empty.{0} (C K)) (F K) := by
    let e : (F K).obj (⊤_ (C K)) ≅ ⊤_ FintypeCat :=
      (terminal_obj_isTerminal K).uniqueUpToIso terminalIsTerminal
    exact preservesTerminal_of_iso (F K) e
  haveI := h
  exact preservesLimitsOfShape_pempty_of_preservesTerminal (G := F K)

-- Field 6: reflection of isomorphisms
theorem bc_reflectsIsos (K : Type) [Field K] : (bc K).ReflectsIsomorphisms where
  reflects {A B} f hf := by
    haveI : IsIso ((bc K).map f).hom :=
      (ObjectProperty.isIso_hom_iff ((bc K).map f)).mpr hf
    have hbij : Function.Bijective (((bc K).map f).hom.hom) := by
      exact (ConcreteCategory.isIso_iff_bijective ((bc K).map f).hom).mp inferInstance
    have hbij' : Function.Bijective (fun x : (AlgebraicClosure K) ⊗[K] (A.obj : Type) =>
        (LinearMap.lTensor (AlgebraicClosure K) f.hom.hom.toLinearMap) x) := by
      change Function.Bijective (fun x : (AlgebraicClosure K) ⊗[K] (A.obj : Type) =>
          (((bc K).map f).hom.hom) x) at hbij
      exact hbij
    have hf' : Function.Bijective f.hom.hom.toLinearMap := by
      exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective (R := K)
        (M := AlgebraicClosure K) (f := f.hom.hom.toLinearMap)).mp hbij'
    have hf'' : Function.Bijective f.hom.hom := hf'
    haveI : IsIso f.hom := (ConcreteCategory.isIso_iff_bijective f.hom).mpr hf''
    exact (ObjectProperty.isIso_hom_iff f).mp inferInstance

theorem reflectsIsos (K : Type) [Field K] [PreGaloisCategory (C K)] :
    (F K).ReflectsIsomorphisms := by
  haveI : ((bc K).op ⋙ E K).ReflectsIsomorphisms := inferInstance
  exact reflectsIsomorphisms_of_iso (fiberIso K).symm

end S1769