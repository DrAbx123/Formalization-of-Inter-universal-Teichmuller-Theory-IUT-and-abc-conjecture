import tmp.sheaf.xif.paper.PaperC3KummerExtensionActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology

-- Local Kummer tensor: actual product carrier over the finite L_v and the
-- exact normed/complete/FinitePadicTensor API that is still missing.
--
-- L_v = completion_v(root_v) is actual and finite over the completion.
-- The root Theta units are actual L_v-units.  The product carrier over L_v
-- is constructed unconditionally.  The local normed-field instance on the
-- IntermediateField L_v, and hence the FinitePadicTensor/Haar/log-volume
-- API, are recorded exactly; no fake NumberField or normed instance is added.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperKummerLocalTensorActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3KummerExtensionActual
open MeasureTheory

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

abbrev KummerLocalField (v : V) : Type u :=
  KummerExtensionField (G := G) v

-- Actual product carrier over the local Kummer fields.
abbrev KummerLocalProductCarrier : Type (max u v) :=
  (v : V) → (KummerLocalField (G := G) v)ˣ

-- Actual root Theta L_v-units and image in the product carrier.
noncomputable def kummerLocalRootThetaUnit
    (j : SignedLabel l.value) (v : V) :
    (KummerLocalField (G := G) v)ˣ :=
  kummerRootThetaUnitInL (G := G) j v

noncomputable def kummerLocalRootThetaPoint
    (j : SignedLabel l.value) : KummerLocalProductCarrier (G := G) :=
  fun v => kummerLocalRootThetaUnit (G := G) j v

noncomputable def kummerLocalRootThetaImageSet :
    Set (KummerLocalProductCarrier (G := G)) :=
  Set.range (kummerLocalRootThetaPoint (G := G))

-- Exact API needed on L_v for the FinitePadicTensor over L_v.
structure KummerLocalTensorAPI (v : V) where
  normedField : NormedField (KummerLocalField (G := G) v)
  completeSpace : CompleteSpace (KummerLocalField (G := G) v)
  measurableSpace : MeasurableSpace (KummerLocalField (G := G) v)
  normedSpaceQp : NormedSpace ℚ_[p] (KummerLocalField (G := G) v)
  finiteDimensionalQp : FiniteDimensional ℚ_[p] (KummerLocalField (G := G) v)
  tensor : Type (max u v)
  tensorMeasurableSpace : MeasurableSpace tensor
  tensor_carrier : Prop
  tensorHaar : @Measure tensor tensorMeasurableSpace

def KummerLocalTensorAPIRequired (v : V) : Prop :=
  Nonempty (KummerLocalTensorAPI (G := G) v)

#check KummerLocalField
#check KummerLocalProductCarrier
#check kummerLocalRootThetaUnit
#check kummerLocalRootThetaPoint
#check kummerLocalRootThetaImageSet
#check KummerLocalTensorAPI
#check KummerLocalTensorAPIRequired

end LeanFormal.IUT.XiFPaper.PaperKummerLocalTensorActual

end