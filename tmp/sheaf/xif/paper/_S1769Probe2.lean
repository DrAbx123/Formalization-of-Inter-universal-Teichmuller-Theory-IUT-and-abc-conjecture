import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.FieldTheory.AbsoluteGaloisGroup

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace S1769Probe

abbrev C (K : Type) [Field K] : Type 1 := (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ

abbrev F (K : Type) [Field K] : C K ⥤ FintypeCat.{0} := CommAlgCat.FiniteEtale.fiber K (AlgebraicClosure K)

variable {K : Type} [Field K]

instance selfInitial' (X : CommAlgCat.FiniteEtale.{0} K) : Unique (CommAlgCat.FiniteEtale.of K K ⟶ X) where
  default := CommAlgCat.FiniteEtale.ofHom (Algebra.ofId K X.obj)
  uniq f := by
    apply InducedCategory.hom_ext
    ext

def selfInitial : IsInitial (CommAlgCat.FiniteEtale.of K K) := IsInitial.ofUnique _

def selfTerminal : IsTerminal (Opposite.op (CommAlgCat.FiniteEtale.of K K)) := selfInitial.op

variable [PreGaloisCategory (C K)]

def terminal_iso_self : (⊤_ (C K)) ≅ Opposite.op (CommAlgCat.FiniteEtale.of K K) :=
  terminalIsTerminal.uniqueUpToIso selfTerminal

theorem terminal_obj_subsingleton : Subsingleton ((F K).obj (⊤_ (C K)) : Type) := by
  let e := (F K).mapIso (terminal_iso_self (K := K))
  let E : ((F K).obj (⊤_ (C K)) : Type) ≃ ((F K).obj (Opposite.op (CommAlgCat.FiniteEtale.of K K)) : Type) :=
    FintypeCat.equivEquivIso.symm e
  haveI : Subsingleton ((F K).obj (Opposite.op (CommAlgCat.FiniteEtale.of K K)) : Type) := by
    change Subsingleton ((CommAlgCat.FiniteEtale.of K K).obj →ₐ[K] AlgebraicClosure K)
    infer_instance
  refine ⟨fun x y => ?_⟩
  apply E.injective
  exact Subsingleton.elim _ _

theorem terminal_obj_nonempty : Nonempty ((F K).obj (⊤_ (C K)) : Type) := by
  let e := (F K).mapIso (terminal_iso_self (K := K))
  let E : ((F K).obj (⊤_ (C K)) : Type) ≃ ((F K).obj (Opposite.op (CommAlgCat.FiniteEtale.of K K)) : Type) :=
    FintypeCat.equivEquivIso.symm e
  exact ⟨E.symm (Algebra.ofId K (AlgebraicClosure K))⟩

def terminal_obj_isTerminal : IsTerminal ((F K).obj (⊤_ (C K))) := by
  haveI : Subsingleton ((F K).obj (⊤_ (C K)) : Type) := terminal_obj_subsingleton (K := K)
  haveI : Nonempty ((F K).obj (⊤_ (C K)) : Type) := terminal_obj_nonempty (K := K)
  refine IsTerminal.ofUniqueHom (fun Y => FintypeCat.homMk (fun _ => Classical.arbitrary _)) ?_
  intro Y m
  apply FintypeCat.hom_ext
  intro y
  exact Subsingleton.elim _ _

theorem preservesTerminal : PreservesLimit (Functor.empty.{0} (C K)) (F K) := by
  let h : (F K).obj (⊤_ (C K)) ≅ ⊤_ FintypeCat :=
    (terminal_obj_isTerminal (K := K)).uniqueUpToIso terminalIsTerminal
  exact preservesTerminal_of_iso (F K) h

theorem preservesTerminalObjects : PreservesLimitsOfShape (Discrete PEmpty.{1}) (F K) := by
  haveI : PreservesLimit (Functor.empty.{0} (C K)) (F K) := preservesTerminal (K := K)
  exact preservesLimitsOfShape_pempty_of_preservesTerminal (G := F K)

end S1769Probe