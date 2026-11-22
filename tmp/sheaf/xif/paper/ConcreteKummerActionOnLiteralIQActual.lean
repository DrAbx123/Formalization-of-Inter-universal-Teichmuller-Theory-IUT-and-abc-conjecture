import tmp.sheaf.xif.paper.ConcreteCompletionImageToLiteralIQActual
import tmp.sheaf.xif.paper.LogKummerCorrespondenceFromSource
import Mathlib.RingTheory.PiTensorProduct

/-!
# Actual Kummer unit action on the concrete literal IQ ambient

The concrete literal IQ ambient is the actual tensor product of the concrete
completion packets at the selected place.  Its tensor factors are commutative
rings, so the tensor product carries the actual multiplication induced by
componentwise multiplication (Mathlib PiTensorProduct.instMul, tprod_mul_tprod).

This file constructs the actual action of the completion unit group on the
concrete literal IQ ambient by left multiplication by the tensor image of the
unit:

  kummerUnitAction j u x = tensorOfUnit j u * x.

The unit and multiplication laws are proved from PiTensorProduct.tprod_mul_tprod
and tensor multiplication associativity.  The actual vertical Kummer layer is
recorded separately.

Exact obstacle: no identification of this completion-unit action with the
SourceTimesMuKummerLayer's TimesMuQuotient action on the tensor packet, i.e. no
multiradial action; that compatibility is not fabricated.

No empty type, no True/PUnit/axiom/sorry, no inequality.  WRITE-ONLY; no local
compile; queued.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.ConcreteKummerActionOnLiteralIQActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource
open LeanFormal.IUT.XiFPaper.ConcreteCompletionImageToLiteralIQActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- The actual tensor image of a completion unit in the concrete literal IQ
ambient: the same unit in every tensor factor. -/
noncomputable def kummerUnitImage
    (j : Nat)
    (u : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ) :
    ConcreteLiteralIQAmbient I place j :=
  completionUnitToConcreteLiteralIQ I place j u

/-- The tensor image is multiplicative. -/
theorem kummerUnitImage_mul
    (j : Nat)
    (u v : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ) :
    kummerUnitImage I place j (u * v) =
      kummerUnitImage I place j u * kummerUnitImage I place j v := by
  unfold kummerUnitImage completionUnitToConcreteLiteralIQ
  rw [PiTensorProduct.tprod_mul_tprod]
  congr 1
  funext x a
  exact Units.val_mul u v

/-- The tensor image of the unit is the tensor unit. -/
theorem kummerUnitImage_one (j : Nat) :
    kummerUnitImage I place j (1 : (CommonPrimeCompletion
      (K := I.initial.arithmetic.Fmod) place)ˣ) =
      (1 : ConcreteLiteralIQAmbient I place j) := by
  unfold kummerUnitImage completionUnitToConcreteLiteralIQ
  rfl

/-- The actual completion-unit action on the concrete literal IQ ambient by
left multiplication with the tensor unit image. -/
noncomputable def kummerUnitAction
    (j : Nat)
    (u : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ) :
    ConcreteLiteralIQAmbient I place j → ConcreteLiteralIQAmbient I place j :=
  fun x => kummerUnitImage I place j u * x

/-- The action of the unit is the identity. -/
theorem kummerUnitAction_one (j : Nat)
    (x : ConcreteLiteralIQAmbient I place j) :
    kummerUnitAction I place j (1 : (CommonPrimeCompletion
      (K := I.initial.arithmetic.Fmod) place)ˣ) x = x := by
  simp [kummerUnitAction, kummerUnitImage_one]

/-- The action is multiplicative in the unit. -/
theorem kummerUnitAction_mul
    (j : Nat)
    (u v : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ)
    (x : ConcreteLiteralIQAmbient I place j) :
    kummerUnitAction I place j (u * v) x =
      kummerUnitAction I place j u (kummerUnitAction I place j v x) := by
  simp [kummerUnitAction, kummerUnitImage_mul, mul_assoc]

/-- The actual vertical Kummer layer at the core strip. -/
noncomputable def actualConcreteKummerLayer :
    SourceTimesMuKummerLayer (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0) :=
  actualVerticalKummerLayer I 0

/-- The actual vertical Kummer arrow at the core strip. -/
noncomputable def actualConcreteKummerArrow :
    SourceKummerArrow (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0) :=
  actualKummerArrow I 0

/-- The actual completion-image map is the qUnit tensor image. -/
theorem concreteCompletionImageToLiteralIQ_eq_kummerImage
    (j : Nat) (idx : ThetaPilotImageIndex (l := l)) :
    concreteCompletionImageToLiteralIQ I place j idx =
      kummerUnitImage I place j (concreteThetaImage I place idx) := rfl

/-- The unit action applied to the concrete completion image. -/
theorem kummerUnitAction_completionImage
    (j : Nat)
    (u : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ)
    (idx : ThetaPilotImageIndex (l := l)) :
    kummerUnitAction I place j u
        (concreteCompletionImageToLiteralIQ I place j idx) =
      kummerUnitImage I place j u *
        kummerUnitImage I place j (concreteThetaImage I place idx) := rfl

end LeanFormal.IUT.XiFPaper.ConcreteKummerActionOnLiteralIQActual
