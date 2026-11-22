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
def terminal_iso_self (K : Type) [Field K] [PreGaloisCategory (C K)] :
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

instance bc_reflectsIsos (K : Type) [Field K] : (bc K).ReflectsIsomorphisms where
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
instance bc_op_reflectsIsos (K : Type) [Field K] : (bc K).op.ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    haveI : IsIso ((bc K).map f.unop) := by
      rw [Functor.op_map] at hf
      exact (isIso_op_iff ((bc K).map f.unop)).mp hf
    have h2 : IsIso f.unop := isIso_of_reflects_iso f.unop (bc K)
    exact (isIso_unop_iff f).mp h2
theorem reflectsIsos (K : Type) [Field K] [PreGaloisCategory (C K)] :
    (F K).ReflectsIsomorphisms := by
  haveI : ((bc K).op ⋙ E K).ReflectsIsomorphisms := inferInstance
  exact reflectsIsomorphisms_of_iso (fiberIso K).symm

def BCPreservesPullbacks (K : Type) [Field K] : Prop :=
  PreservesLimitsOfShape WalkingCospan (bc K).op
def BCPreservesFiniteProducts (K : Type) [Field K] : Prop :=
  PreservesFiniteProducts (bc K)
def BCPreservesEpis (K : Type) [Field K] : Prop :=
  Functor.PreservesEpimorphisms (bc K).op
def BCPreservesQuotients (K : Type) [Field K] : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PreservesColimitsOfShape (SingleObj G) (bc K).op

theorem preservesPullbacks_of (K : Type) [Field K] [PreGaloisCategory (C K)]
    (h : BCPreservesPullbacks K) :
    PreservesLimitsOfShape WalkingCospan (F K) := by
  haveI : PreservesLimitsOfShape WalkingCospan (bc K).op := h
  haveI : PreservesLimitsOfShape WalkingCospan (E K) := inferInstance
  haveI : PreservesLimitsOfShape WalkingCospan ((bc K).op ⋙ E K) := inferInstance
  exact preservesLimitsOfShape_of_natIso (fiberIso K).symm

theorem preservesFiniteCoproducts_of (K : Type) [Field K] [PreGaloisCategory (C K)]
    (h : BCPreservesFiniteProducts K) :
    PreservesFiniteCoproducts (F K) where
  preserves n := by
    haveI : PreservesFiniteProducts (bc K) := h
    haveI : PreservesFiniteCoproducts (bc K).op := preservesFiniteCoproducts_op (bc K)
    haveI : PreservesFiniteCoproducts (E K) := inferInstance
    haveI : PreservesFiniteCoproducts ((bc K).op ⋙ E K) := inferInstance
    exact preservesColimitsOfShape_of_natIso (fiberIso K).symm

theorem preservesEpis_of (K : Type) [Field K] [PreGaloisCategory (C K)]
    (h : BCPreservesEpis K) :
    Functor.PreservesEpimorphisms (F K) := by
  haveI : Functor.PreservesEpimorphisms (bc K).op := h
  haveI : Functor.PreservesEpimorphisms ((bc K).op ⋙ E K) := inferInstance
  exact Functor.preservesEpimorphisms.of_iso (fiberIso K).symm

theorem preservesQuotients_of (K : Type) [Field K] [PreGaloisCategory (C K)]
    (h : BCPreservesQuotients K) :
    ∀ (G : Type) [Group G] [Finite G], PreservesColimitsOfShape (SingleObj G) (F K) := by
  intro G _ _
  haveI := h G
  haveI : PreservesColimitsOfShape (SingleObj G) (E K) := inferInstance
  haveI : PreservesColimitsOfShape (SingleObj G) ((bc K).op ⋙ E K) := inferInstance
  exact preservesColimitsOfShape_of_natIso (fiberIso K).symm

@[implicit_reducible]
def fiberFunctorOf (K : Type) [Field K] [PreGaloisCategory (C K)]
    (hPull : BCPreservesPullbacks K)
    (hCoprod : BCPreservesFiniteProducts K)
    (hEpi : BCPreservesEpis K)
    (hQuot : BCPreservesQuotients K) :
    PreGaloisCategory.FiberFunctor (F K) where
  preservesTerminalObjects := preservesTerminalObjects K
  preservesPullbacks := preservesPullbacks_of K hPull
  preservesFiniteCoproducts := preservesFiniteCoproducts_of K hCoprod
  preservesEpis := preservesEpis_of K hEpi
  preservesQuotientsByFiniteGroups := preservesQuotients_of K hQuot
  reflectsIsos := reflectsIsos K

end S1769