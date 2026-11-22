/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemSigma

/-!
# Consumer: Sigma family of systems of Frobenioids

Projects a component of a Sigma-assembled family of systems, its base category,
and its Definition 1.3 axiom package.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota : Type u} (kappa : iota -> Type u)
variable (system : (index : iota) -> FrobenioidSystem (kappa index))

noncomputable def sigmaPresentation (index : Sigma kappa) :
    FrobenioidPresentation.{u} :=
  (sigma kappa system).presentation index

@[simp] theorem sigmaPresentation_eq (index : Sigma kappa) :
    sigmaPresentation kappa system index =
      (system index.1).presentation index.2 :=
  rfl

noncomputable def sigmaAxiomsConsumer (index : Sigma kappa) :
    (sigmaPresentation kappa system index).preFrobenioid.FrobenioidAxioms :=
  (sigmaPresentation kappa system index).axioms

@[simp] theorem sigmaAxiomsConsumer_eq (index : Sigma kappa) :
    sigmaAxiomsConsumer kappa system index =
      ((system index.1).presentation index.2).axioms :=
  rfl

noncomputable def sigmaBaseCategoryConsumer (index : Sigma kappa) :
    CategoryTheory.Cat.{u, u} :=
  (sigma kappa system).baseCategory index

@[simp] theorem sigmaBaseCategoryConsumer_eq (index : Sigma kappa) :
    sigmaBaseCategoryConsumer kappa system index =
      (system index.1).baseCategory index.2 :=
  rfl

theorem sigmaBaseCategoryConsumer_isConnected (index : Sigma kappa) :
    CategoryTheory.IsConnected
      (sigmaBaseCategoryConsumer kappa system index) :=
  (sigma kappa system).baseCategory_isConnected index

end FrobenioidSystem

#check FrobenioidSystem.sigmaPresentation
#check FrobenioidSystem.sigmaAxiomsConsumer

end Iut
