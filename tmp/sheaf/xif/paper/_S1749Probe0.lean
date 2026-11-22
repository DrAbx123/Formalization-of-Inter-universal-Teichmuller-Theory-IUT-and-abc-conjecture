import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.RingTheory.Etale.Finite
universe u
open CategoryTheory CategoryTheory.Limits
namespace Probe
variable (K : Type u) [Field K]
abbrev C : Type (u+1) := (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ
noncomputable abbrev dummyF : C ⥤ FintypeCat.{u} := (Functor.const C).obj (FintypeCat.of PUnit)
abbrev FF (hPre : PreGaloisCategory C) : Prop := @PreGaloisCategory.FiberFunctor C _ hPre (dummyF K)
#check @FF
#check @GaloisCategory.mk
#check @PreGaloisCategory.functorToContAction
#check @PreGaloisCategory.FiberFunctor
end Probe
