/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemAxiomsFamily

/-!
# Consumer: dependent Frobenioid axiom family

Unpacks the dependent family of Definition 1.3 axiom packages carried by a
system of Frobenioids.  This is the consumer form used by downstream system
and gluing constructions of IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota : Type u} (system : FrobenioidSystem iota)

/-- Consumer view of the dependent axiom family. -/
noncomputable def axiomsFamilyConsumer :
    (index : iota) ->
      (system.presentation index).preFrobenioid.FrobenioidAxioms :=
  system.axiomsFamily

@[simp] theorem axiomsFamilyConsumer_apply (index : iota) :
    system.axiomsFamilyConsumer index = system.axiomsFamily index :=
  rfl

noncomputable def axiomsFamilyConsumer_axioms (index : iota) :
    (system.presentation index).preFrobenioid.FrobenioidAxioms :=
  system.axiomsFamilyConsumer index

end FrobenioidSystem

#check FrobenioidSystem.axiomsFamilyConsumer
#check FrobenioidSystem.axiomsFamilyConsumer_apply
#check FrobenioidSystem.axiomsFamilyConsumer_axioms

end Iut
