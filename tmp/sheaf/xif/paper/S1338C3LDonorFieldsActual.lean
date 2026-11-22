import tmp.sheaf.xif.paper.S1314C3GaloisRootActionActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.Theorem311Source.S1338C3LDonorFieldsActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source.ConcreteC3RootTensorActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3RootCompletionActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open LeanFormal.IUT.XiFPaper.S1314C3GaloisRootActionActual
universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
structure ConcreteC3DonorLFields where
  qUnitAlgClosure : (ConcreteQAlgebraicClosure (I := I) place)ˣ
  qUnitAlgClosure_eq : qUnitAlgClosure =
    concreteQUnitAlgebraicClosure (I := I) place
  roots : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place)
  roots_eq : roots = concreteRootsAlgebraicClosure (I := I) place
  roots' : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place)
  roots'_eq : roots' = concreteRootsPrimeAlgebraicClosure (I := I) place
  kummerClass :
    (ConcreteQAlgebraicClosure (I := I) place ≃ₐ[
      CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place]
      ConcreteQAlgebraicClosure (I := I) place) →
      CyclotomicTower (ConcreteQAlgebraicClosure (I := I) place)
  kummerClass_eq : ∀ σ, kummerClass σ = actualC3KummerClass I place σ
  rootChange :
    (ConcreteQAlgebraicClosure (I := I) place ≃ₐ[
      CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place]
      ConcreteQAlgebraicClosure (I := I) place) →
      CyclotomicTower (ConcreteQAlgebraicClosure (I := I) place)
  rootChange_eq : ∀ σ, rootChange σ = actualC3RootChange I place σ
noncomputable def actualConcreteC3DonorLFields :
    ConcreteC3DonorLFields (I := I) place where
  qUnitAlgClosure := concreteQUnitAlgebraicClosure (I := I) place
  qUnitAlgClosure_eq := rfl
  roots := concreteRootsAlgebraicClosure (I := I) place
  roots_eq := rfl
  roots' := concreteRootsPrimeAlgebraicClosure (I := I) place
  roots'_eq := rfl
  kummerClass := actualC3KummerClass (I := I) place
  kummerClass_eq := by intro σ; rfl
  rootChange := actualC3RootChange (I := I) place
  rootChange_eq := by intro σ; rfl
theorem actualConcreteC3DonorLFields_roots_pow
    (n : Nat) (hn : n ≠ 0) :
    (actualConcreteC3DonorLFields (I := I) place).roots.root n ^ n =
      concreteQUnitAlgebraicClosure (I := I) place :=
  NatRootSystem.pow_self _ n hn
theorem actualConcreteC3DonorLFields_rootChange_eq_diff
    (σ : ConcreteQAlgebraicClosure (I := I) place ≃ₐ[
      CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place]
      ConcreteQAlgebraicClosure (I := I) place) :
    (actualConcreteC3DonorLFields (I := I) place).rootChange σ =
      KummerClass.rootSystemDiff
        (concreteRootsAlgebraicClosure (I := I) place)
        (galoisRootsAction I place σ
          (concreteRootsAlgebraicClosure (I := I) place)) :=
  actualC3RootChange_eq (I := I) place σ
theorem actualConcreteC3DonorLFields_kummerClass_eq_rootChange
    (σ : ConcreteQAlgebraicClosure (I := I) place ≃ₐ[
      CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place]
      ConcreteQAlgebraicClosure (I := I) place) :
    (actualConcreteC3DonorLFields (I := I) place).kummerClass σ =
      (actualConcreteC3DonorLFields (I := I) place).rootChange σ :=
  actualC3KummerClass_eq_rootChange (I := I) place σ
def completionRootFieldObstruction : Prop :=
  Nonempty (NatRootSystem (concreteC3QUnit (I := I) place))
end LeanFormal.IUT.Theorem311Source.S1338C3LDonorFieldsActual
