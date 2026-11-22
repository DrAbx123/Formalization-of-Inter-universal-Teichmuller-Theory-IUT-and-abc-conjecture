import tmp.sheaf.n8.closure.C7QPilotMassActual
import tmp.sheaf.n8.closure.EtaQOAddHaarNormalizedCalibrationActual

/-!
# C7 q-pilot mass transport

One-factor transport targets: the image of the actual normalized C6 unit
region is the Kf integer ring, the raw C6 Haar transports to the Kf additive
Haar, and consequently the normalized tensor mass is the Kf normalized qO
mass.  No arbitrary transport equality is asserted; each is a named exact
obligation.
-/

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.C7QPilotMassTransport

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7QPilotMassActual
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

local instance (S : SourceInitialThetaData l) : MeasurableSpace (PaperKf S) := borel _
local instance (S : SourceInitialThetaData l) : BorelSpace (PaperKf S) := ⟨rfl⟩
local instance (S : SourceInitialThetaData l) : MeasurableSpace (Block S) :=
  (rawData (places S) (tuple S)).measurableSpace
local instance (S : SourceInitialThetaData l) : BorelSpace (Block S) :=
  (rawData (places S) (tuple S)).borelSpace

noncomputable def paperKfAddHaar (S : SourceInitialThetaData l) : Measure (PaperKf S) :=
  (Measure.addHaar : Measure (PaperKf S))

noncomputable def paperKfIntegersMass (S : SourceInitialThetaData l) : ENNReal :=
  paperKfAddHaar S (Integers (PaperKf S) : Set (PaperKf S))

noncomputable def paperKfNormalizedHaar (S : SourceInitialThetaData l) : Measure (PaperKf S) :=
  (paperKfIntegersMass S)⁻¹ • paperKfAddHaar S

/-- One-factor image of the actual normalized C6 unit region. -/
noncomputable def c6UnitRegionImage (S : SourceInitialThetaData l) : Set (PaperKf S) :=
  Set.image (fun y => e S y)
    (c6UnitRegion (places S) (tuple S) (rawData (places S) (tuple S)))

/-- Exact unit-region transport. -/
def UnitRegionTransport (S : SourceInitialThetaData l) : Prop :=
  c6UnitRegionImage S = (Integers (PaperKf S) : Set (PaperKf S))

/-- Transported normalized C6 Haar. -/
noncomputable def mappedNormalizedData (S : SourceInitialThetaData l) : Measure (PaperKf S) :=
  Measure.map (fun y => e S y)
    (c6TensorNormalizedData (places S) (tuple S))

/-- Exact raw-Haar transport. -/
def RawHaarTransport (S : SourceInitialThetaData l) : Prop :=
  Measure.map (fun y => e S y)
    (rawData (places S) (tuple S)).mu = paperKfAddHaar S

/-- Exact qO mass formula for the normalized tensor measure. -/
def QPilotMassFormula (S : SourceInitialThetaData l) : Prop :=
  (qPilotMass S).toReal = ‖q S‖ ^ (d S)

/-- Exact d-normalized paper log-q formula. -/
def QPaperTransportFormula (S : SourceInitialThetaData l) : Prop :=
  QPaperPerDegree S = Real.log ‖q S‖

end LeanFormal.IUT.N8Closure.C7QPilotMassTransport

end