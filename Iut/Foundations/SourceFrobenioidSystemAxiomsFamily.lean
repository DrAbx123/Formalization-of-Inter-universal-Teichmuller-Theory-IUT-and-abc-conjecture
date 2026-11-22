/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystem

/-!
# Axiom families of a system of Frobenioids

Each component of a system of Frobenioids carries the full Definition 1.3
axiom package.  This file packages those packages as a dependent family.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota : Type u} (system : FrobenioidSystem iota)

/-- The dependent family of Frobenioid axioms. -/
noncomputable def axiomsFamily :
    (index : iota) ->
      (system.presentation index).preFrobenioid.FrobenioidAxioms :=
  fun index => (system.presentation index).axioms

@[simp] theorem axiomsFamily_apply (index : iota) :
    system.axiomsFamily index = (system.presentation index).axioms :=
  rfl

end FrobenioidSystem

#check FrobenioidSystem.axiomsFamily
#check FrobenioidSystem.axiomsFamily_apply

end Iut
