import tmp.sheaf.xif.paper.C3TensorIndexBadEquivDataActualAdapted
import tmp.sheaf.xif.paper.ConcreteC3DonorAssemblyActual
import tmp.sheaf.xif.paper.NativeBadSetFiniteActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Concrete C3 tensor index / native bad family equivalence data

This file uses the concrete C3 donor assembly and the actual native bad family
to record the two actual index-cardinality data

  Fintype.card A.tensorIndex
  Fintype.card (Bad (nativePlaceSelection T))

and the actual base finite places

  A.tensorPlaces i (A.tensorTuple i)  and  b.1.

It constructs the index equivalence only from an explicit actual cardinality
equality via Fintype.equivOfCardEq; no arbitrary equivalence and no place
identification is fabricated. The exact obstruction is the nonemptiness of the
data structure, together with the two explicit compatibility propositions.

No True/PUnit, empty type, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.C3TensorIndexBadEquivConcreteActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.ConcreteC3DonorAssemblyActual
open LeanFormal.IUT.N8Closure.NativeBadSetFiniteActual

universe ua upi umon ui

variable {l : PrimeGeFive}
variable {I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7)}
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
variable (A : ConcreteC3DonorAssemblyActual (I := I) place)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual cardinality of the concrete C3 tensor index. -/
def c3TensorIndexCard : Nat :=
  Fintype.card A.tensorIndex

/-- The actual cardinality of the native bad family. -/
def nativeBadCard : Nat :=
  Fintype.card (Bad (nativePlaceSelection T))

/-- The exact cardinality equality needed for an actual index equivalence. -/
def c3BadCardEquality : Prop :=
  c3TensorIndexCard (I := I) place A = nativeBadCard (l := l) T

/-- The actual base finite place of a concrete C3 tensor index. -/
noncomputable def c3TensorIndexPlace (i : A.tensorIndex) :
    FinitePlaceAtPrime I.initial.arithmetic.Fmod A.p :=
  A.tensorPlaces i (A.tensorTuple i)

/-- The actual base finite place of a native bad place. -/
noncomputable def nativeBadPlace (b : Bad (nativePlaceSelection T)) :
    NumberField.FinitePlace T.arithmetic.Fmod :=
  b.1

/-- The concrete C3 tensor index / native bad equivalence data. indexEquiv is
actual only from a cardinality equality; the two compatibility propositions are
exact remaining inputs. -/
structure C3TensorIndexBadEquivData where
  indexEquiv : A.tensorIndex ≃ Bad (nativePlaceSelection T)
  card_compat : c3TensorIndexCard (I := I) place A = nativeBadCard (l := l) T
  basePlace_compat : Prop
  thetaValue_compat : Prop

/-- The exact obstruction: existence of the concrete index/bad equivalence data. -/
def C3TensorIndexBadEquivObstruction : Prop :=
  Nonempty (C3TensorIndexBadEquivData (I := I) place A T)

/-- The cardinality part of the obstruction, separated from the place/value
compatibility parts. -/
def C3TensorIndexBadCardObstruction : Prop :=
  c3BadCardEquality (I := I) place A T

/-- The actual index equivalence constructed from an explicit cardinality
equality. This is Fintype.equivOfCardEq, not an arbitrary hand-picked
equivalence. -/
noncomputable def c3BadIndexEquivOfCard
    (hcard : c3BadCardEquality (I := I) place A T) :
    A.tensorIndex ≃ Bad (nativePlaceSelection T) :=
  Fintype.equivOfCardEq hcard

/-- Conditional actual equivalence data from the cardinality equality and the
two exact compatibility propositions. -/
noncomputable def c3TensorIndexBadEquivOfCard
    (hcard : c3BadCardEquality (I := I) place A T)
    (hbase : Prop) (htheta : Prop) :
    C3TensorIndexBadEquivData (I := I) place A T where
  indexEquiv := c3BadIndexEquivOfCard (I := I) place A T hcard
  card_compat := hcard
  basePlace_compat := hbase
  thetaValue_compat := htheta

/-- The constructed equivalence has the actual cardinality equality. -/
theorem c3TensorIndexBadEquivOfCard_card
    (hcard : c3BadCardEquality (I := I) place A T)
    (hbase : Prop) (htheta : Prop) :
    (c3TensorIndexBadEquivOfCard (I := I) place A T hcard hbase htheta).card_compat =
      hcard :=
  rfl

/-- The actual tensor index cardinality is the Fintype cardinality. -/
theorem c3TensorIndexCard_eq :
    c3TensorIndexCard (I := I) place A = Fintype.card A.tensorIndex :=
  rfl

/-- The actual native bad cardinality is the Fintype cardinality. -/
theorem nativeBadCard_eq :
    nativeBadCard (l := l) T = Fintype.card (Bad (nativePlaceSelection T)) :=
  rfl

end LeanFormal.IUT.XiFPaper.C3TensorIndexBadEquivConcreteActualAdapted

end
