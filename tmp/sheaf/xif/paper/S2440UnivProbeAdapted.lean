import tmp.sheaf.xif.paper.S2439D9ProofActual
noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2134D9DescentActual
namespace Probe2440
universe v u v' u'
section
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (A : Type u') [Category.{v'} A]
def E : Prop := ∀ (S : C) (R : Presieve S), Sieve.generate R ∈ J S → HasEffectiveDescentPresieve (J.pseudofunctorOver A) R
def EAll : Prop := ∀ (C : Type u) [Category.{v} C] (J : GrothendieckTopology C) (A : Type u') [Category.{v'} A], E (C := C) J A
def S : Prop := (J.pseudofunctorOver A).IsStack J
def SAll : Prop := ∀ (C : Type u) [Category.{v} C] (J : GrothendieckTopology C) (A : Type u') [Category.{v'} A], S (C := C) J A
end
variable {K : Type u} [Field K]
set_option pp.universes true in
#check (inferInstance : Category (Iut.SchemeOverField K))
set_option pp.universes true in
#check (inferInstance : Category (Type u))
-- instantiate the all-sites prop at the D9 site
example : SAll.{u, u+1, u, u+1} := by
  intro C _ J A _
  exact (J.pseudofunctorOver A).IsStack J
example : EAll.{u, u+1, u, u+1} := by
  intro C _ J A _ S R hR
  exact hasEffectiveDescentPresieve_of_generate_top (J.pseudofunctorOver A) R hR
-- the direct instantiation statement form
example (h : SAll.{u, u+1, u, u+1}) :
    (Iut.SchemeOverField K).etaleTopology = (Iut.SchemeOverField.etaleTopology K) := rfl
end Probe2440
end
