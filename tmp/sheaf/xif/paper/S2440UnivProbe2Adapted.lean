import tmp.sheaf.xif.paper.S2439D9ProofActual
noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
namespace Probe2440c
universe v u v' u' w
section
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (A : Type u') [Category.{v'} A]
def SS : Prop := (J.pseudofunctorOver A).IsStack J
def EE : Prop := ∀ (S0 : C) (R : Presieve S0), Sieve.generate R ∈ J S0 → HasEffectiveDescentPresieve (J.pseudofunctorOver A) R
def SAll : Prop := ∀ (C : Type u) [Category.{v} C] (J : GrothendieckTopology C), SS (C := C) J (Type w)
def EAll : Prop := ∀ (C : Type u) [Category.{v} C] (J : GrothendieckTopology C), EE (C := C) J (Type w)
end
set_option pp.universes true in
#check @SAll
set_option pp.universes true in
#check SAll.{u, u+1, u}
#check EAll.{u, u+1, u}
variable {K : Type u} [Field K]
example (h : SAll.{u, u+1, u}) :
    (Iut.SchemeOverField.etaleTopology K) = (Iut.SchemeOverField.etaleTopology K) := rfl
example (h : EAll.{u, u+1, u}) : True := trivial
end Probe2440c
end
