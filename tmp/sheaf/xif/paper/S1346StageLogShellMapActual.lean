import tmp.sheaf.xif.paper.S1327Ind3IntegralLogShellActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIntegerQuotient

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# S1346: actual stage-to-log-shell map, or the exact first field

## What is checked

* S1266/S1315 put the (Ind3) data on the actual times-mu quotient stage
  Ind3Stage I n m v = TimesMuQuotient ((I.fPrimeStripAt n m).Mon v)^x.
* S1313 builds the tensor packet from the actual integral log-shell
  actualIntegralLogShell I vQ v, whose carrier is the actual range
  (p*_v)^{-1} * unitLog (O^x).
* The two definitions do not share a carrier.  In particular the stage unit
  group is the units of the abstract value monoid Mon v of an arbitrary
  OriginalInput, while the shell is a subtype of the actual completion
  CommonPrimeCompletion v.

## Actual canonical map

At the level of the actual integral units there is a canonical map, and it
is an isomorphism, not an identity:

  TimesMuQuotient ((Integers K)^x)  =*  Multiplicative (integralLogShell K p)

constructed by descending the actual unit logarithm unitLog through its
kernel CommGroup.torsion; scaledUnitLogToShellHom is surjective and its
kernel is exactly the torsion subgroup.  This is actualUnitLogShellEquiv
and its monoid-hom form actualUnitLogShellMap.  The map sends a class [u]
to (p*_v)^{-1} * unitLog u; this formula is the logarithm construction,
not the identity.

## Exact first field at the Ind3 stage

The actual integral-unit equivalence cannot be applied to Ind3Stage without
a comparison from the stage units to the actual integral units.  The exact
first field is recorded as StageUnitLogComparison:

* a place place : IntegralPlaceTotal I (the place comparison already named
  by S1327), and
* a monoid hom unitMap : ((I.fPrimeStripAt n m).Mon v)^x ->* (Integers K)^x
  whose composite with unitLog kills the torsion of the stage unit group.

No inhabitant of StageUnitLogComparison is constructed or asserted.
Given such a datum, stageLogShellMap is constructed; its value on a quotient
class is (p*_v)^{-1} * unitLog (unitMap u).  Thus the construction is
genuinely logarithmic and is not an identity map between the stage and the
shell.

## Tensor packet

The tensor packet is a tensor product over the capsule labels of the direct
sums of the shells over the places.  A single stage shell therefore does not
determine an element of the tensor packet: one must choose a capsule label and
a pure tensor in the complementary factors.  The exact first field is recorded
as StageToTensorPacketFirstField; no label-independent map and no arbitrary
choice of complementary factors are supplied or asserted here.

No PUnit, no one-point shell, no arbitrary constant map, no new axiom and no
sorry are used.
-/

namespace LeanFormal.IUT.XiFPaper.S1346StageLogShellMapActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1327Ind3IntegralLogShellActual
open LeanFormal.IUT.XiFPaper.S1313IntegralLogShellContractActual
open LeanFormal.IUT.XiFPaper.S1266SourceInd3Actual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

local instance integralValuationFact (vQ : ActualIntegralValuation) :
    Fact (Nat.Prime vQ.1) := ⟨vQ.2⟩

/-! ## 1. The actual unit-logarithm quotient equivalence -/

/-- If the actual unit logarithm of an integral unit is zero, then the scaled
unit logarithm is the identity of the log-shell.  This is the exact
torsion-killing step used below. -/
theorem scaledUnitLogToShellHom_eq_one_of_unitLog_eq_zero
    (vQ : ActualIntegralValuation) (v : actualIntegralPlace I vQ)
    (u : (Integers (CommonPrimeCompletion v))ˣ)
    (hu : unitLog (K := CommonPrimeCompletion v) u = 0) :
    scaledUnitLogToShellHom (K := CommonPrimeCompletion v) (p := vQ.1) u = 1 := by
  apply Multiplicative.ofAdd.injective
  change (⟨(logShellScale vQ.1 : CommonPrimeCompletion v)⁻¹ * unitLog u,
    ⟨u, rfl⟩⟩ : integralLogShell (K := CommonPrimeCompletion v) (p := vQ.1)) = 0
  apply Subtype.ext
  change (logShellScale vQ.1 : CommonPrimeCompletion v)⁻¹ * unitLog u =
    (0 : CommonPrimeCompletion v)
  rw [hu, mul_zero]

/-- The kernel of the actual scaled unit logarithm is exactly the full torsion
subgroup of the integral units.  This is the actual kernel computation; it is
not assumed. -/
theorem scaledUnitLogToShellHom_ker
    (vQ : ActualIntegralValuation) (v : actualIntegralPlace I vQ) :
    (scaledUnitLogToShellHom (K := CommonPrimeCompletion v) (p := vQ.1)).ker =
      CommGroup.torsion (Integers (CommonPrimeCompletion v))ˣ := by
  ext u
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have hsub : (⟨(logShellScale vQ.1 : CommonPrimeCompletion v)⁻¹ * unitLog u,
        ⟨u, rfl⟩⟩ : integralLogShell (K := CommonPrimeCompletion v) (p := vQ.1)) = 0 := by
      apply Multiplicative.ofAdd.injective
      rw [show scaledUnitLogToShellHom (K := CommonPrimeCompletion v) (p := vQ.1) u =
        Multiplicative.ofAdd (⟨(logShellScale vQ.1 : CommonPrimeCompletion v)⁻¹ * unitLog u,
          ⟨u, rfl⟩⟩ : integralLogShell (K := CommonPrimeCompletion v) (p := vQ.1)) from rfl] at h
      exact h
    have hlog : (logShellScale vQ.1 : CommonPrimeCompletion v)⁻¹ * unitLog u = 0 :=
      congrArg Subtype.val hsub
    have hscale : (logShellScale vQ.1 : CommonPrimeCompletion v) ≠ 0 :=
      Nat.cast_ne_zero.mpr (ne_of_gt (logShellScale_pos (p := vQ.1)))
    have hzero : unitLog (K := CommonPrimeCompletion v) u = 0 :=
      (mul_eq_zero.mp hlog).resolve_left (inv_ne_zero hscale)
    exact (unitLog_eq_zero_iff_isOfFinOrder (p := vQ.1) u).mp hzero
  · intro hu
    exact scaledUnitLogToShellHom_eq_one_of_unitLog_eq_zero I vQ v u
      ((unitLog_eq_zero_iff_isOfFinOrder (p := vQ.1) u).mpr hu)

/-- The actual canonical equivalence between the times-mu quotient of the
integral units and the actual integral log-shell.  It is induced by the actual
scaled unit logarithm; it is not an identity. -/
noncomputable def actualUnitLogShellEquiv (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    TimesMuQuotient ((Integers (CommonPrimeCompletion v))ˣ) ≃*
      Multiplicative ↥(actualIntegralLogShell I vQ v) :=
  QuotientGroup.liftEquiv (N := CommGroup.torsion (Integers (CommonPrimeCompletion v))ˣ)
    (scaledUnitLogToShellHom_surjective (K := CommonPrimeCompletion v) (p := vQ.1))
    (scaledUnitLogToShellHom_ker I vQ v).symm

/-- The monoid-hom form of the actual canonical map. -/
noncomputable def actualUnitLogShellMap (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    TimesMuQuotient ((Integers (CommonPrimeCompletion v))ˣ) →*
      Multiplicative ↥(actualIntegralLogShell I vQ v) :=
  (actualUnitLogShellEquiv I vQ v).toMonoidHom

/-- On quotient classes the actual map is exactly the scaled actual
logarithm. -/
@[simp] theorem actualUnitLogShellMap_quotientMap (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) (u : (Integers (CommonPrimeCompletion v))ˣ) :
    actualUnitLogShellMap I vQ v (TimesMuQuotient.quotientMap u) =
      scaledUnitLogToShellHom (K := CommonPrimeCompletion v) (p := vQ.1) u := rfl

/-- Additive-hom form of the actual canonical map, from the additive version
of the times-mu quotient to the log-shell module itself. -/
noncomputable def actualUnitLogShellAddHom (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    Additive (TimesMuQuotient ((Integers (CommonPrimeCompletion v))ˣ)) →+
      ↥(actualIntegralLogShell I vQ v) :=
  (actualUnitLogShellMap I vQ v).toAdditive

/-! ## 2. Exact first field at the Ind3 stage -/

/-- The raw unit comparison needed at the stage: a monoid hom from the units of
the abstract value monoid Mon v to the actual integral units of a chosen
completion.  This is the first field that OriginalInput does not supply. -/
abbrev StageUnitMap (n m : Int) (v : V) (place : IntegralPlaceTotal I) :
    Type (max umon ua) :=
  ((I.fPrimeStripAt n m).Mon v)ˣ →*
    (Integers (CommonPrimeCompletion place.2))ˣ

/-- The exact first field for a canonical stage-to-log-shell map: a place and
a unit comparison whose composite with the actual logarithm kills the torsion
of the stage unit group.  No inhabitant is constructed or asserted. -/
structure StageUnitLogComparison (n m : Int) (v : V) where
  /-- The actual place at which the shell is taken. -/
  place : IntegralPlaceTotal I
  /-- The comparison from the stage units to the actual integral units. -/
  unitMap : StageUnitMap I n m v place
  /-- The logarithm of the comparison kills the stage torsion, so it descends
      to the times-mu quotient. -/
  torsion_log_zero : ∀ u ∈ CommGroup.torsion ((I.fPrimeStripAt n m).Mon v)ˣ,
    unitLog (K := CommonPrimeCompletion place.2) (unitMap u) = 0

/-- The exact open proposition: an inhabitant of the first-field structure.
This is not proved. -/
def StageUnitLogComparisonRequired (n m : Int) (v : V) : Prop :=
  Nonempty (StageUnitLogComparison I n m v)

/-- The logarithm of the unit comparison, as a monoid hom to the additive
local field in multiplicative notation. -/
noncomputable def stageUnitLogHom (n m : Int) (v : V)
    (d : StageUnitLogComparison I n m v) :
    ((I.fPrimeStripAt n m).Mon v)ˣ →* Multiplicative (CommonPrimeCompletion d.place.2) :=
  (unitLogHom (K := CommonPrimeCompletion d.place.2) (p := d.place.1.1)).comp d.unitMap

/-- The stage torsion is in the kernel of the compared logarithm. -/
theorem stageUnitLogHom_torsion_zero (n m : Int) (v : V)
    (d : StageUnitLogComparison I n m v) :
    CommGroup.torsion ((I.fPrimeStripAt n m).Mon v)ˣ ≤
      MonoidHom.ker (stageUnitLogHom I n m v d) := by
  intro u hu
  rw [MonoidHom.mem_ker]
  change Multiplicative.ofAdd
    (unitLog (K := CommonPrimeCompletion d.place.2) (d.unitMap u)) = 1
  rw [d.torsion_log_zero u hu]
  rfl

/-- The compared logarithm descended to the actual times-mu quotient stage. -/
noncomputable def stageUnitLogQuotientHom (n m : Int) (v : V)
    (d : StageUnitLogComparison I n m v) :
    Ind3Stage I n m v →* Multiplicative (CommonPrimeCompletion d.place.2) :=
  QuotientGroup.lift (CommGroup.torsion ((I.fPrimeStripAt n m).Mon v)ˣ)
    (stageUnitLogHom I n m v d) (stageUnitLogHom_torsion_zero I n m v d)

/-- The conditional canonical stage-to-log-shell map.  Its value on a quotient
class is the scaled actual logarithm of the compared integral unit. -/
noncomputable def stageLogShellMap (n m : Int) (v : V)
    (d : StageUnitLogComparison I n m v) :
    Ind3Stage I n m v →*
      Multiplicative ↥(actualIntegralLogShell I d.place.1 d.place.2) :=
  QuotientGroup.lift (CommGroup.torsion ((I.fPrimeStripAt n m).Mon v)ˣ)
    ((scaledUnitLogToShellHom (K := CommonPrimeCompletion d.place.2)
      (p := d.place.1.1)).comp d.unitMap)
    (by
      intro u hu
      exact scaledUnitLogToShellHom_eq_one_of_unitLog_eq_zero I d.place.1 d.place.2
        (d.unitMap u) (d.torsion_log_zero u hu))

/-- The exact formula of the conditional map on quotient classes: it is the
scaled actual unit logarithm, not the identity. -/
@[simp] theorem stageLogShellMap_quotientMap (n m : Int) (v : V)
    (d : StageUnitLogComparison I n m v)
    (u : ((I.fPrimeStripAt n m).Mon v)ˣ) :
    stageLogShellMap I n m v d (TimesMuQuotient.quotientMap u) =
      scaledUnitLogToShellHom (K := CommonPrimeCompletion d.place.2)
        (p := d.place.1.1) (d.unitMap u) := rfl

/-- The underlying local-field value of the map is the paper's scaled
logarithm. -/
theorem stageLogShellMap_formula (n m : Int) (v : V)
    (d : StageUnitLogComparison I n m v)
    (u : ((I.fPrimeStripAt n m).Mon v)ˣ) :
    (stageLogShellMap I n m v d (TimesMuQuotient.quotientMap u)).toAdd =
      (logShellScale d.place.1.1 : CommonPrimeCompletion d.place.2)⁻¹ *
        unitLog (K := CommonPrimeCompletion d.place.2) (d.unitMap u) := by
  rw [stageLogShellMap_quotientMap]
  rfl

/-- Additive-hom form of the conditional stage map, from the additive version
of the times-mu stage to the integral log-shell module. -/
noncomputable def stageLogShellAddHom (n m : Int) (v : V)
    (d : StageUnitLogComparison I n m v) :
    Additive (Ind3Stage I n m v) →+
      ↥(actualIntegralLogShell I d.place.1 d.place.2) :=
  (stageLogShellMap I n m v d).toAdditive

/-! ## 3. Exact first field for the tensor packet -/

/-- The integral tensor packet at capsule level j and valuation vQ. -/
abbrev IntegralTensorPacket (j : Nat) (vQ : ActualIntegralValuation) : Type (max 0 ua) :=
  TensorPacket (integralLogShellFamily I j) vQ

/-- The complement of a chosen capsule label in the tensor packet: one element
of each other direct-sum factor.  These are exactly the data needed to form a
pure tensor with a chosen stage-shell element. -/
abbrev StageTensorComplement (d : StageUnitLogComparison I n m v) (j : Nat)
    (label : Capsule j) : Type ua :=
  (i : Capsule j) → i ≠ label →
    DirectSumFactor (integralLogShellFamily I j) d.place.1 i

/-- The exact first field for a map from the stage to the integral tensor
packet: a stage comparison, a chosen capsule label, and a pure tensor in the
complementary factors.  No label-independent map is asserted. -/
structure StageToTensorPacketFirstField (n m : Int) (v : V) (j : Nat) where
  /-- The stage comparison and the chosen actual place. -/
  comparison : StageUnitLogComparison I n m v
  /-- The capsule label at which the stage shell is inserted. -/
  label : Capsule j
  /-- The complementary direct-sum factors. -/
  complement : StageTensorComplement (I := I) comparison j label

/-- The exact open proposition for the tensor-packet first field.  No
inhabitant is constructed or asserted. -/
def StageToTensorPacketFirstFieldRequired (n m : Int) (v : V) (j : Nat) : Prop :=
  Nonempty (StageToTensorPacketFirstField (I := I) n m v j)

/-! ## 4. Axiom probes -/

#print axioms scaledUnitLogToShellHom_eq_one_of_unitLog_eq_zero
#print axioms scaledUnitLogToShellHom_ker
#print axioms actualUnitLogShellEquiv
#print axioms actualUnitLogShellMap
#print axioms actualUnitLogShellMap_quotientMap
#print axioms actualUnitLogShellAddHom
#print axioms StageUnitLogComparison
#print axioms stageUnitLogHom_torsion_zero
#print axioms stageUnitLogQuotientHom
#print axioms stageLogShellMap
#print axioms stageLogShellMap_quotientMap
#print axioms stageLogShellMap_formula
#print axioms stageLogShellAddHom
#print axioms StageToTensorPacketFirstField

end LeanFormal.IUT.XiFPaper.S1346StageLogShellMapActual
