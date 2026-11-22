import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import tmp.sheaf.xif.paper.S3133ModelM1PlaceToModActual
import tmp.sheaf.xif.paper.S3133ModelM2bDescentActual

/-!
# Adaptation onto the EXISTING concrete model (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: qpilot in-model R1 composition,
mainline/lattice inventory, abc scaling wrapper.

PRIOR ART / RE-SCOPE (Lead-approved): the concrete model already exists in
LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceUnitRegionHaarDataActual.lean:
sourceHaarActualFamily (322), sourceHaarActualOriginalInput (346),
sourceHaarActualImageRealization (374), sourceHaarActualData (416) with
unitRegion/scaling/degreeBound and the three record fields.  We do NOT rebuild
the model.  This file is the single adaptation layer: it names the existing
model input/realization/Haar data and wires qpilot's two in-model additions
(M1 explicit placeToMod datum, M2b definitional qVFamily) onto it, and records
why the nontrivial procession scaling (baseUnit completion scalar, abc's
wrapper) is needed: the existing model's value monoid is the nonpositive reals,
whose unit group is trivial (scaling = 1).
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3133ExistingModelAdaptationActual

local instance s3133AdaptFivePrimeFact : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3133ModelM1PlaceToModActual
open LeanFormal.IUT.XiFPaper.S3133ModelM2bDescentActual

variable {l : PrimeGeFive}

/-- The existing concrete model input (reuse, not a new construction). -/
abbrev S3133TreeModelInput (S : SourceDefinition31Data l) : OriginalInput l Unit :=
  sourceHaarActualOriginalInput (l := l) S

/-- The existing concrete model realization (reuse). -/
noncomputable abbrev S3133TreeModelRealization (S : SourceDefinition31Data l) :
    (S3133TreeModelInput S).SourceImageRealization () :=
  sourceHaarActualImageRealization (l := l) S

/-- The existing concrete Haar/unit-region data (reuse). -/
noncomputable abbrev S3133TreeModelHaarData (S : SourceDefinition31Data l)
    (n : ThetaPilotCarrier l) :
    (S3133TreeModelInput S).SourceUnitRegionHaarData ()
      (S3133TreeModelRealization S) n :=
  sourceHaarActualData (l := l) S n

/-- The existing model's scaling is the monoid unit (trivial unit group: the
value monoid is the nonpositive reals).  The nontrivial procession scaling must
therefore be carried by a completion scalar (abc's baseUnit wrapper). -/
theorem S3133TreeModelHaarData_scaling (S : SourceDefinition31Data.{0} l)
    (n : ThetaPilotCarrier l) :
    (S3133TreeModelHaarData S n).scaling = 1 :=
  sourceHaarActualData_scaling (l := l) S n

/-- The existing model's theta q-parameter is 1 at every index. -/
theorem S3133TreeModel_theta_q (S : SourceDefinition31Data.{0} l) (n m : Int) :
    ((S3133TreeModelInput S).theaterAt n m).thetaPacket.q = 1 :=
  sourceHaarActual_originalInput_theta_q (l := l) S n m

/-- The model q-parameter value used by the in-model M2b descent. -/
def S3133TreeModelQValue : Real := 1

/-- The model theta q equals the model q-parameter value (rfl). -/
theorem S3133TreeModel_theta_q_eq (S : SourceDefinition31Data.{0} l) (n m : Int) :
    ((S3133TreeModelInput S).theaterAt n m).thetaPacket.q = S3133TreeModelQValue :=
  sourceHaarActual_originalInput_theta_q (l := l) S n m

/-- In-model M1 place-to-moduli datum for the EXISTING model (V = Unit). -/
structure S3133TreeModelPlaceToModDatum where
  /-- the model moduli place type -/
  V_mod : Type
  /-- the model place map (V_mod_bijection source datum) -/
  placeOf : V_mod → Unit
  /-- faithfulness of the model place map -/
  placeOf_injective : Function.Injective placeOf

/-- In-model M1 datum on the existing model: the single moduli place maps to the
single place of Unit; injective by construction. -/
noncomputable def S3133TreeModelM1Datum : S3133TreeModelPlaceToModDatum where
  V_mod := Unit
  placeOf := fun _ => ()
  placeOf_injective := by
    intro a b _
    exact Subsingleton.elim a b

/-- In-model M1 is constructible on the existing model (V = Unit). -/
theorem S3133TreeModelM1_constructible :
    ∃ D : S3133TreeModelPlaceToModDatum, Function.Injective D.placeOf :=
  ⟨S3133TreeModelM1Datum, S3133TreeModelM1Datum.placeOf_injective⟩

/-- In-model M2b qVFamily: defined from the model q (definitional descent). -/
noncomputable def S3133TreeModelQVFam (_v : Unit) : Real := S3133TreeModelQValue

/-- In-model M2b descent: definitional. -/
theorem S3133TreeModelQVFam_descent (v : Unit) :
    S3133TreeModelQVFam v = S3133TreeModelQValue :=
  rfl

/-- The nontrivial procession scaling datum (abc wrapper): a genuine Q_5 unit
with unit norm, acting on the completion side (the existing model's value monoid
cannot carry it). -/
structure S3133TreeModelBaseUnitScaling where
  baseUnit : (ℚ_[5])ˣ
  baseUnit_norm_one : ‖((baseUnit : ℚ_[5]))‖ = 1

end LeanFormal.IUT.XiFPaper.S3133ExistingModelAdaptationActual
