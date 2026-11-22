/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemSumConsumer

/-!
# Consumer: axioms of the disjoint-union system

Each summand component carries its own Definition 1.3 axiom package.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota kappa : Type u}

noncomputable def sumAxiomsConsumer
    (left : FrobenioidSystem iota) (right : FrobenioidSystem kappa)
    (index : iota ⊕ kappa) :
    (sumPresentation left right index).preFrobenioid.FrobenioidAxioms :=
  (sumPresentation left right index).axioms

@[simp] theorem sumAxiomsConsumer_inl
    (left : FrobenioidSystem iota) (right : FrobenioidSystem kappa)
    (index : iota) :
    sumAxiomsConsumer left right (Sum.inl index) =
      (left.presentation index).axioms :=
  rfl

@[simp] theorem sumAxiomsConsumer_inr
    (left : FrobenioidSystem iota) (right : FrobenioidSystem kappa)
    (index : kappa) :
    sumAxiomsConsumer left right (Sum.inr index) =
      (right.presentation index).axioms :=
  rfl

end FrobenioidSystem

#check FrobenioidSystem.sumAxiomsConsumer
#check FrobenioidSystem.sumAxiomsConsumer_inl
#check FrobenioidSystem.sumAxiomsConsumer_inr

end Iut
