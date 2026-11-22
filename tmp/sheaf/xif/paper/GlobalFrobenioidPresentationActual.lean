import tmp.sheaf.xif.paper.GlobalRealifiedFrobenioidActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackend
import Iut.Foundations.Frobenioid

/-! # Global realified Frobenioid C^⊩mod: actual FrobenioidPresentation

Source: IUT I, Example 3.5, (i); IUT III, Example 3.6, (ii); [FrdI],
Definition 1.1-1.3.  The repository already constructs the actual global model
Frobenioid presentation from the number-field effective-divisor cone:

  Example36.SourceModelBackend.numberFieldFrobenioidPresentation K.

This file reuses that actual construction for the base number field Fmod.  It
does not fabricate FrobenioidAxioms: the full FrobenioidPresentation, its
DivisorialMonoidOn, structureFunctor, connectedness, total-epimorphicity, and
axioms are the actual fields of the existing presentation.

No inequality/equality is judged. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.GlobalFrobenioidPresentationActual

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend
open CategoryTheory
open Iut

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The actual global model Frobenioid presentation (IUT III Example 3.6(ii)). -/
noncomputable def globalFrobenioidPresentationActual :
    Iut.FrobenioidPresentation :=
  numberFieldFrobenioidPresentation (F := K)

/-- The actual base category of the presentation, the one-object model base. -/
noncomputable def globalFrobenioidBaseActual : CategoryTheory.Cat :=
  (globalFrobenioidPresentationActual (K := K)).baseCategory

/-- The actual carrier category of the presentation. -/
noncomputable def globalFrobenioidCarrierActual : CategoryTheory.Cat :=
  (globalFrobenioidPresentationActual (K := K)).carrier

/-- The actual pre-Frobenioid of the presentation. -/
noncomputable def globalFrobenioidPreActual :
    PreFrobenioid
      (globalFrobenioidCarrierActual (K := K) : Type u)
      (globalFrobenioidBaseActual (K := K) : Type u)
      (globalFrobenioidPresentationActual (K := K)).isFSM :=
  (globalFrobenioidPresentationActual (K := K)).preFrobenioid

/-- The actual DivisorialMonoidOn of the presentation. -/
noncomputable def globalFrobenioidDivisorMonoidActual :
    DivisorialMonoidOn (BottomBase.{u}) BottomFSM :=
  (globalFrobenioidPreActual (K := K)).divisorMonoid

/-- The actual structure functor to the elementary Frobenioid. -/
noncomputable def globalFrobenioidStructureFunctorActual :
    (globalFrobenioidCarrierActual (K := K) : Type u) ⥤
      ElementaryFrobenioid (BottomBase.{u}) BottomFSM
        (globalFrobenioidDivisorMonoidActual (K := K)) :=
  (globalFrobenioidPreActual (K := K)).structureFunctor

/-- The actual FrobenioidAxioms of the presentation. -/
noncomputable def globalFrobenioidAxiomsActual :
    (globalFrobenioidPreActual (K := K)).FrobenioidAxioms :=
  (globalFrobenioidPresentationActual (K := K)).axioms

/-- The actual carrier connectedness witness. -/
theorem globalFrobenioidCarrierConnectedActual :
    CategoryTheory.IsConnected (globalFrobenioidCarrierActual (K := K)) :=
  (globalFrobenioidPresentationActual (K := K)).carrierConnected

/-- The actual base connectedness witness. -/
theorem globalFrobenioidBaseConnectedActual :
    CategoryTheory.IsConnected (globalFrobenioidBaseActual (K := K)) :=
  (globalFrobenioidPresentationActual (K := K)).baseConnected

/-- The actual carrier total-epimorphicity witness. -/
theorem globalFrobenioidCarrierTotallyEpimorphicActual :
    ∀ {A B : (globalFrobenioidCarrierActual (K := K) : Type u)} (f : A ⟶ B), Epi f :=
  (globalFrobenioidPresentationActual (K := K)).carrierTotallyEpimorphic

/-- The actual base total-epimorphicity witness. -/
theorem globalFrobenioidBaseTotallyEpimorphicActual :
    ∀ {A B : (globalFrobenioidBaseActual (K := K) : Type u)} (f : A ⟶ B), Epi f :=
  (globalFrobenioidPresentationActual (K := K)).baseTotallyEpimorphic

/-- The actual global model divisor monoid on the one-object bottom base:
the effective divisor cone with identity pullbacks. -/
noncomputable def globalEffectiveDivisorMonoidActual :
    DivisorialMonoidOn (BottomBase.{u}) BottomFSM :=
  globalDivisorMonoidOn (F := K)

end LeanFormal.IUT.XiFPaper.GlobalFrobenioidPresentationActual

end
