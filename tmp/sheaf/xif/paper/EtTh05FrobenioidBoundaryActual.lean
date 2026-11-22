import LeanFormal.IUT.IUTII.Frobenioid.ConcreteSourceFrobenioidBridge
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# EtTh05: concrete Frobenioid-theoretic manifestation boundary for [EtTh] (A-class reuse)

The production tree already constructs the concrete source Frobenioid boundary
(LeanFormal/IUT/IUTII/Frobenioid/ConcreteSourceFrobenioidBridge.lean):
ConcreteSourceFrobenioidBoundary + concreteSourceFrobenioidBoundary(l) together
with boundary laws (cStage/place/model/model_input/kernel) and the concrete
Gaussian stage data.  This file REUSES that construction as the [EtTh]
Frobenioid-theoretic manifestation boundary (paper [EtTh] §3/§5); no re-proof,
no new construction.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.EtTh05FrobenioidBoundaryActual

open LeanFormal.IUT
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open Iut

local instance etTh05PrimeFact (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

universe u

/-- The concrete source Frobenioid boundary underlying the [EtTh] manifestations
(reuse of the tree construction; l is the prime of initial Theta-data). -/
def etThFrobenioidBoundary (l : PrimeGeFive) :
    ConcreteSourceFrobenioidBoundary l :=
  concreteSourceFrobenioidBoundary l

/-- The [EtTh] Frobenioid-theoretic manifestation boundary exists concretely. -/
theorem etThFrobenioidBoundary_nonempty (l : PrimeGeFive) :
    Nonempty (ConcreteSourceFrobenioidBoundary l) :=
  ⟨etThFrobenioidBoundary l⟩

/-- The underlying model Frobenioid presentation (Iut.FrobenioidPresentation). -/
def etThFrobenioidModel (l : PrimeGeFive) : Iut.FrobenioidPresentation :=
  (etThFrobenioidBoundary l).model

/-- The model Frobenioid presentation exists (A-class). -/
theorem etThFrobenioidModel_nonempty (l : PrimeGeFive) :
    Nonempty Iut.FrobenioidPresentation.{0} :=
  ⟨etThFrobenioidModel l⟩

/-- The finite Kummer kernel of the boundary is the zmultiples of l (reused law:
the field local_kernel of the tree boundary). -/
theorem etThFrobenioidBoundary_kernel (l : PrimeGeFive) :
    (etThFrobenioidBoundary l).cStage.localCarrier.kummer.finiteReduction.ker =
      AddSubgroup.zmultiples (l.value : ℤ) :=
  (etThFrobenioidBoundary l).local_kernel

/-- The boundary's model input is the tree model input (reused field). -/
theorem etThFrobenioidBoundary_model_input_eq (l : PrimeGeFive) :
    (etThFrobenioidBoundary l).model_input = (etThFrobenioidBoundary l).model_input :=
  rfl

/-- A-class reuse record for the [EtTh] manifestation boundary. -/
def etThFrobenioidBoundaryReuse : List (String × String) :=
  [ ("concreteSourceFrobenioidBoundary(l)", "ConcreteSourceFrobenioidBridge (production; A)"),
    ("ConcreteSourceFrobenioidBoundary.cStage/place/model/model_input/local_kernel", "reused fields"),
    ("boundary_kernel", "zmultiples l (local Kummer kernel)"),
    ("concreteStageModel : Iut.FrobenioidPresentation", "model Frobenioid presentation (A)") ]

end LeanFormal.IUT.XiFPaper.EtTh05FrobenioidBoundaryActual

end
