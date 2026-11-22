/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystem

/-!
# Sigma family of systems of Frobenioids

A family of systems indexed by `iota`, with fiber index types `kappa i`,
assembles into one system on the sigma type.  This is the data-level
family operation needed for place/label systems in IUTchI, Definition
6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota : Type u}
variable (kappa : iota -> Type u)
variable (system : (index : iota) -> FrobenioidSystem (kappa index))

/-- Sigma assembly of a family of systems. -/
def sigma : FrobenioidSystem (Sigma kappa) where
  presentation := fun index => (system index.1).presentation index.2

@[simp] theorem sigma_apply (index : Sigma kappa) :
    (sigma kappa system).presentation index =
      (system index.1).presentation index.2 :=
  rfl

end FrobenioidSystem

#check FrobenioidSystem.sigma
#check FrobenioidSystem.sigma_apply

end Iut
