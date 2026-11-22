/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1391C3LSourcePilotActual
import Mathlib.Tactic

/-! # A965: generic SourcePilotRegionDataL over arbitrary V (new file; original untouched) -/

/- S1391's `SourcePilotRegionDataL` fixes `I : OriginalInput l (FinitePrimePlace 2 7)`.
Here we copy the structure with `{V : Type*} (I : OriginalInput l V)`; the fields are
V-agnostic: they use only `I`, a finite place of `I.initial.arithmetic.Fmod`, the
algebraic-closure q unit/root block and the tensor block. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1SourcePilotLGenericActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3RootTensorActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3RootCompletionActual
open LeanFormal.IUT.XiFPaper.S1314C3GaloisRootActionActual
open LeanFormal.IUT.Theorem311Source.S1338C3LDonorFieldsActual
open LeanFormal.IUT.XiFPaper.S1219ConcreteTensorLandingActual
open LeanFormal.IUT.XiFPaper.S1267TensorUnitActual
open LeanFormal.IUT.XiFPaper.S1349C3LDonorRestructureActual
open LeanFormal.IUT.Theorem311Source.S1354C3LDonorRestructureActual

universe ua uv upi umon ui

variable {l : PrimeGeFive}

/-- Generic copy of `SourcePilotRegionDataL`: same fields for arbitrary `V`. -/
structure SourcePilotRegionDataLGeneric {V : Type uv}
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  p : Nat
  [hp : Fact p.Prime]
  place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p
  q : FinitePlaceQCandidate place.val
  thetaPacket : FiniteThetaPacket l
  qUnit : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ
  qUnit_eq : qUnit = candidateUnits (K := I.initial.arithmetic.Fmod) place q
  qUnitAlgClosure_eq :
    concreteQUnitAlgebraicClosure place =
      Units.map
        (algebraMap (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
          (ConcreteQAlgebraicClosure place)).toMonoidHom qUnit
  roots : NatRootSystem (concreteQUnitAlgebraicClosure place)
  roots' : NatRootSystem (concreteQUnitAlgebraicClosure place)
  kummerClass : C3LGalois I place →
    CyclotomicTower (ConcreteQAlgebraicClosure place)
  rootChange : C3LGalois I place →
    CyclotomicTower (ConcreteQAlgebraicClosure place)
  kummerClass_eq_rootChange : ∀ σ, kummerClass σ = rootChange σ
  rootChange_eq : ∀ σ, rootChange σ =
    KummerClass.rootSystemDiff roots (galoisRootsAction I place σ roots)
  tensorIndex : Type
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex → Type
  tensorPlaces : (i : tensorIndex) → tensorPlaceIndex i →
    FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p
  tensorTuple : (i : tensorIndex) → tensorPlaceIndex i
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ
  tensorLanding : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place →
    ArithmeticTensorTupleBlock tensorPlaces tensorTuple
  tensorLanding_q : tensorLanding
    (q.q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) =
    (tensorUnit : ArithmeticTensorTupleBlock tensorPlaces tensorTuple)

attribute [instance] SourcePilotRegionDataLGeneric.hp
attribute [instance] SourcePilotRegionDataLGeneric.tensorFintype

def genericRows : List (String × String) :=
  [ ("SourcePilotRegionDataLGeneric", "structure copy over arbitrary V (fields V-agnostic)") ,
    ("p / place / q / qUnit", "finite place data of I.initial.arithmetic.Fmod") ,
    ("roots/kummerClass/rootChange", "algebraic-closure block (I-only)") ,
    ("tensorIndex/tensorPlaces/tensorUnit/tensorLanding", "tensor block (I and place only)") ,
    ("generic constructor actualSourcePilotRegionDataL", "not attempted in this first pass") ]

theorem genericRows_length : genericRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1SourcePilotLGenericActual
