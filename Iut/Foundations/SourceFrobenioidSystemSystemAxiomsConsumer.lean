/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemAxiomsFamilyConsumer

/-!
# Downstream consumer: per-component system Frobenioid axioms

Consumes the dependent axiom family consumer and exposes, for each index, the
actual Definition 1.3 axiom package of the component.  This is the
component-level consumer used by system assembly and gluing (IUTchI,
Definition 6.13, (i)).
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota : Type u} (system : FrobenioidSystem iota)

/-- The component axiom package, as a downstream consumer. -/
noncomputable def systemAxiomsConsumer (index : iota) :
    (system.presentation index).preFrobenioid.FrobenioidAxioms :=
  system.axiomsFamilyConsumer_axioms index

@[simp] theorem systemAxiomsConsumer_eq (index : iota) :
    system.systemAxiomsConsumer index =
      system.axiomsFamilyConsumer index :=
  rfl

noncomputable def systemAxiomsConsumer_isActual (index : iota) :
    (system.presentation index).preFrobenioid.FrobenioidAxioms :=
  system.systemAxiomsConsumer index

end FrobenioidSystem

#check FrobenioidSystem.systemAxiomsConsumer
#check FrobenioidSystem.systemAxiomsConsumer_eq
#check FrobenioidSystem.systemAxiomsConsumer_isActual

end Iut
