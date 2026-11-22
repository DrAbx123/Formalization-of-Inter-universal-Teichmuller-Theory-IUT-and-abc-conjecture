import tmp.sheaf.xif.paper.S1161CoreChoiceBridgeActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceColumnCarrierIdentification

/-! # S1167: concrete Core Choice + LinkSpan and the first exact gap

Reuses S1161 and the concrete finite input.  `concreteInput l` carries an
actual `Carrier` and hence an actual `Core (finiteLabel l) (ProcessionChoice l)`;
`LinkSpan.refl` gives an actual LinkSpan.  This is a finite concrete instance
(R6), not a general `SourceFTimesMuPrimeStrip V → Core Label Choice` bridge:
no such map exists in the tree.  The first exact gap is the source-level
choice carrier/realization; the FPrimeStrip-side data alone do not determine a
`Choice` type or its `Core` laws. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1167ConcreteCoreBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.ParametricTheorem311
open LeanFormal.IUT.Theorem311Source.PolyIsoTransport
open LeanFormal.IUT.SourceProcessionBoundary
open LeanFormal.IUT.SourceColumnRealization

universe u v

/-- Actual concrete core from the Q(i)-at-5 finite input. -/
noncomputable def concreteCore (l : PrimeGeFive) :
    MultiradialKernel.Core (ConcreteFiniteTheorem311.finiteLabel l)
      (ConcreteFiniteTheorem311.ProcessionChoice l) :=
  (Input.concreteInput l).carrier.core

/-- Actual LinkSpan on the concrete core. -/
noncomputable def concreteLinkSpan (l : PrimeGeFive) :
    LinkSpan (concreteCore l) (concreteCore l) :=
  LinkSpan.refl (concreteCore l)

@[simp] theorem concreteLinkSpan_left
    (l : PrimeGeFive) (c : ConcreteFiniteTheorem311.ProcessionChoice l) :
    (concreteLinkSpan l).left c = c := rfl

@[simp] theorem concreteLinkSpan_right
    (l : PrimeGeFive) (c : ConcreteFiniteTheorem311.ProcessionChoice l) :
    (concreteLinkSpan l).right c = c := rfl

/-- R6: concrete finite readback. -/
theorem concreteReadback (l : PrimeGeFive) (N : Nat) :
    RealizationReadback (l := l) (N := N) (concreteCore l)
      (AddMonoidHom.id (ConcreteFiniteTheorem311.finiteLabel l))
      (concreteCore l).base :=
  by
    simpa [concreteCore] using concreteInput_readback l N

#check concreteCore
#check concreteLinkSpan
#check concreteReadback
#check SourceFTimesMuPrimeStrip
#check SourceFTimesMuPrimeStrip.canonical
#check SourceFTimesMuPrimeStripEquivalence
#check SourceFTimesMuPrimeStripFullPolyIsomorphism

end LeanFormal.IUT.XiFPaper.S1167ConcreteCoreBridgeActual
end
