import tmp.sheaf.xif.paper.PaperSourceGeometryActual
import tmp.sheaf.xif.paper.PaperBadPlaceTensorGeometryActual

/-!
# S12: bridge between fixed-p and dependent-p completion geometries

CompletionValuedSourceGeometry (l := l) (K) (p) V has a fixed prime p and,
besides the place map, actual qUnit and thetaPacket fields.

DependentCompletionValuedGeometry K has an index type and a place map whose
places may have different rational primes.

This file constructs:

* fixedToDependent: fixed-p geometry -> dependent-p geometry with the same
  index (requires Fintype V);
* commonPrimeIndex: the actual subtype of dependent indices whose prime is p;
* DependentHasCommonPrime: the exact common-prime condition for the full
  reverse bridge;
* DependentCompletionQData: the exact additional qUnit/thetaPacket data needed
  to make the reverse bridge a CompletionValuedSourceGeometry;
* fixedOfDependentOfQData: the exact conditional reverse bridge.

The dependent geometry does not carry qUnit/thetaPacket, so the fixed geometry
cannot be reconstructed from places alone. That missing data is recorded, not
fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S12CompletionGeometryBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {l : PrimeGeFive} {V : Type} {p : Nat} [Fact p.Prime]

/-- Fixed-p geometry as a dependent-p geometry (same index). -/
noncomputable def fixedToDependent [Fintype V]
    (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V) :
    DependentCompletionValuedGeometry K where
  index := V
  indexFintype := inferInstance
  place v :=
    { p := p
      hp := inferInstance
      place := G.place v }

/-- The constructed dependent place has prime p. -/
@[simp] theorem fixedToDependent_place [Fintype V]
    (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V) (v : V) :
    ((fixedToDependent (l := l) (K := K) (p := p) G).place v).p = p :=
  rfl

/-- The dependent place is exactly the original fixed place. -/
@[simp] theorem fixedToDependent_place_eq [Fintype V]
    (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V) (v : V) :
    ((fixedToDependent (l := l) (K := K) (p := p) G).place v).place = G.place v :=
  rfl

/-- The actual common-prime index of a dependent geometry. -/
def commonPrimeIndex (D : DependentCompletionValuedGeometry K) (p : Nat) : Type :=
  {i : D.index // (D.place i).p = p}

/-- Exact common-prime condition for reconstructing the full fixed geometry. -/
def DependentHasCommonPrime (D : DependentCompletionValuedGeometry K) (p : Nat) : Prop :=
  forall i : D.index, (D.place i).p = p

/-- Exact additional data missing from the dependent geometry: qUnit and
thetaPacket data for a fixed completion geometry. -/
structure DependentCompletionQData
    (D : DependentCompletionValuedGeometry K) (p : Nat) [Fact p.Prime]
    (h : DependentHasCommonPrime D p) where
  qUnit : (i : D.index) →
    CompletionValueCarrier (h i ▸ (D.place i).place)
  thetaPacket : FiniteThetaPacket l
  thetaPacket_q_eq : ∀ i : D.index,
    thetaPacket.q = ‖(qUnit i : CommonPrimeCompletion (h i ▸ (D.place i).place))‖

/-- Conditional reverse bridge: common prime plus the actual q data gives the
fixed-p CompletionValuedSourceGeometry. -/
noncomputable def fixedOfDependentOfQData
    (D : DependentCompletionValuedGeometry K) (p : Nat) [Fact p.Prime]
    (h : DependentHasCommonPrime D p)
    (Q : DependentCompletionQData (l := l) D p h) :
    CompletionValuedSourceGeometry (l := l) (K := K) (p := p) D.index where
  place i := (h i) ▸ (D.place i).place
  qUnit := Q.qUnit
  thetaPacket := Q.thetaPacket
  thetaPacket_q_eq := Q.thetaPacket_q_eq

/-- The reverse bridge's place is the common-prime place. -/
@[simp] theorem fixedOfDependentOfQData_place
    (D : DependentCompletionValuedGeometry K) (p : Nat) [Fact p.Prime]
    (h : DependentHasCommonPrime D p)
    (Q : DependentCompletionQData (l := l) D p h) (i : D.index) :
    (fixedOfDependentOfQData (l := l) D p h Q).place i =
      (h i) ▸ (D.place i).place :=
  rfl

/-- Exact missing proposition for the reverse bridge: common prime and q data. -/
def DependentToFixedBridgeMissing
    (D : DependentCompletionValuedGeometry K) (p : Nat) [Fact p.Prime] : Prop :=
  ∃ h : DependentHasCommonPrime D p,
    Nonempty (DependentCompletionQData (l := l) D p h)

end LeanFormal.IUT.XiFPaper.S12CompletionGeometryBridgeActual

end
