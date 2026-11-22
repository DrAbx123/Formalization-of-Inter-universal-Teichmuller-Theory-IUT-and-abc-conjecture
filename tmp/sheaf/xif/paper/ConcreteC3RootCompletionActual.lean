import tmp.sheaf.xif.paper.ConcreteC3RootTensorActual
import LeanFormal.IUT.IUTII.Kummer.KummerClass

/-!
# Concrete C3 roots in the completion algebraic closure

The completion K is not algebraically closed, so no NatRootSystem in K-units is
constructed.  In its algebraic closure L = AlgebraicClosure K we have the actual
compatible root system from ConcreteC3RootTensorActual:

  roots, roots' : NatRootSystem (image of qUnit in L).

This file packages the actual usable roots and their actual root-change tower:

  rootChange := KummerClass.rootSystemDiff roots roots'
             : CyclotomicTower L,

with the root-change equation definitional, plus the power laws for roots and
roots'.

The completion-root obstruction and tensor-landing obstruction from
ConcreteC3RootTensorActual are re-exported as the exact remaining objects; no
landing map or root in K is fabricated.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.Theorem311Source.ConcreteC3RootCompletionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source.ConcreteC3RootTensorActual

universe ua upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- Actual usable roots/roots' and root-change data in the algebraic closure of
the concrete completion. -/
structure ConcreteC3RootCompletionActual where
  qUnit : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ
  qUnitAlgClosure : (ConcreteQAlgebraicClosure (I := I) place)ˣ
  qUnitAlgClosure_eq : qUnitAlgClosure =
    Units.map
      (algebraMap (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
        (ConcreteQAlgebraicClosure (I := I) place)).toMonoidHom qUnit
  roots : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place)
  roots_eq : roots = concreteRootsAlgebraicClosure (I := I) place
  roots' : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place)
  roots'_eq : roots' = concreteRootsPrimeAlgebraicClosure (I := I) place
  rootChange : CyclotomicTower
    (ConcreteQAlgebraicClosure (I := I) place)
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'

/-- The actual roots/roots' and root-change data. -/
noncomputable def concreteC3RootCompletionActual :
    ConcreteC3RootCompletionActual (I := I) place where
  qUnit := concreteC3QUnit (I := I) place
  qUnitAlgClosure := concreteQUnitAlgebraicClosure (I := I) place
  qUnitAlgClosure_eq := rfl
  roots := concreteRootsAlgebraicClosure (I := I) place
  roots_eq := rfl
  roots' := concreteRootsPrimeAlgebraicClosure (I := I) place
  roots'_eq := rfl
  rootChange := KummerClass.rootSystemDiff
    (concreteRootsAlgebraicClosure (I := I) place)
    (concreteRootsPrimeAlgebraicClosure (I := I) place)
  rootChange_eq := rfl

namespace ConcreteC3RootCompletionActual

variable (R : ConcreteC3RootCompletionActual (I := I) place)

/-- The usable roots object. -/
def usableRoots : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place) :=
  R.roots

/-- The usable roots' object. -/
def usableRootsPrime : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place) :=
  R.roots'

/-- The usable root-change tower. -/
def usableRootChange : CyclotomicTower
    (ConcreteQAlgebraicClosure (I := I) place) :=
  R.rootChange

/-- The root-change tower is exactly the Kummer root-system difference. -/
theorem usableRootChange_eq_diff :
    R.usableRootChange = KummerClass.rootSystemDiff R.usableRoots R.usableRootsPrime :=
  R.rootChange_eq

/-- The actual roots satisfy the power law. -/
theorem usableRoots_pow (n : Nat) (hn : n ≠ 0) :
    R.usableRoots.root n ^ n =
      concreteQUnitAlgebraicClosure (I := I) place :=
  NatRootSystem.pow_self R.usableRoots n hn

/-- The actual roots' satisfy the power law. -/
theorem usableRootsPrime_pow (n : Nat) (hn : n ≠ 0) :
    R.usableRootsPrime.root n ^ n =
      concreteQUnitAlgebraicClosure (I := I) place :=
  NatRootSystem.pow_self R.usableRootsPrime n hn

/-- The root-change component is the quotient of the two root families. -/
theorem usableRootChange_component (n : Nat) :
    R.usableRootChange.component n =
      R.usableRootsPrime.root n / R.usableRoots.root n := by
  rw [usableRootChange, R.rootChange_eq]
  rfl

end ConcreteC3RootCompletionActual

/-- The exact completion-root obstruction remains: no root system in the
completion itself. -/
def completionRootSystemObstruction : Prop :=
  ConcreteCompletionRootObstruction (I := I) place

/-- The exact tensor-landing obstruction remains: no concrete tensor landing
data. -/
def tensorLandingObstruction : Prop :=
  ConcreteTensorLandingObstruction (I := I) place

/-- The completion-root obstruction is exactly the missing NatRootSystem in the
completion. -/
theorem completionRootSystemObstruction_iff :
    completionRootSystemObstruction (I := I) place ↔
      Nonempty (NatRootSystem (concreteC3QUnit (I := I) place)) :=
  Iff.rfl

/-- The tensor obstruction is exactly the missing concrete landing datum. -/
theorem tensorLandingObstruction_iff :
    tensorLandingObstruction (I := I) place ↔
      Nonempty (ConcreteTensorLandingData (I := I) place) :=
  Iff.rfl

end LeanFormal.IUT.Theorem311Source.ConcreteC3RootCompletionActual

end
