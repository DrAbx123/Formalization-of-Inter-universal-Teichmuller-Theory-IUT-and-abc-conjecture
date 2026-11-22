/- U-C Step (viii) (beta): collection layer from the actual T data (kurt).

Decision (approved by Lead, agreed with david): the collection index type is the
per-packet tensor factor index set qVFamTensorV (T side = Unit), NOT the set of
bad places; the bad-place aggregation is the outer layer (gamma_b =
nativeBadLocalWeight).

The per-label hull volume V is the normalized log-volume of the ACTUAL hull (of
the possible images), supplied as a region family argument; david instantiates
it with the actual holomorphic hull so that the accepted StepV donor
(arithmeticTuple_stepV_normalizedLogVolume_le_paperBound) directly provides the
hV inequality.  Definitions only, no proofs, no sorry.

To keep the definitions light (avoid the default-heartbeat isDefEq timeout that
appears when the concrete tensor block type is unfolded inside a definition),
the hull-log and norm-order helpers are stated generically over an arbitrary
tensor block / normed field. -/
import tmp.sheaf.xif.paper.Mzk1URQNormalizationActual
import tmp.sheaf.xif.paper.Mzk1URPacketActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URCollectionLayerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open MeasureTheory

universe u v w

/-! ## Generic helpers (light; no concrete tensor block unfolded) -/

section Generic

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

/-- The actual normalized log-volume of a tensor region (generic form; the
concrete T-side region is supplied at the use site). -/
noncomputable def urCollHullLog
    (S : Set (ArithmeticTensorTupleBlock places tuple)) : ℝ :=
  arithmeticTupleNormalizedLogVolume places tuple Measure.addHaar S

/-- The actual local norm order of a supplied field element (the actual local
different element is supplied at the use site). -/
noncomputable def urCollLocalNormOrder {F : Type*} [NormedField F] (x : F) : ℝ :=
  localNormOrder p x

end Generic

/-! ## Actual T-side packet data -/

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The per-packet collection index type: the actual tensor factor index set. -/
abbrev UrCollIndex : Type := qVFamTensorV

/-- The log of the actual packet prime. -/
noncomputable def urCollLogp : ℝ := Real.log (qVFamTensorP T b : ℝ)

/-- The collection weight family (trivial on the single-factor T packet). -/
noncomputable def urCollLam : UrCollIndex → ℝ := fun _ => 1

/-- The actual q order at the tensor factor: the actual normalized qVFamily
coefficient (equal to the actual localNormOrder of the qVFamily q). -/
noncomputable def urCollOq : UrCollIndex → ℝ :=
  fun _ => qVFamNormalizedCoefficient T b

/-- The paper constant iota times l*_mod, passed explicitly for now (paper
letters are supplied by U-L/U-C donors). -/
noncomputable def urCollIotaL (iota : ℝ) : ℝ := iota

#print urCollLogp
#print urCollLam
#print urCollOq
#print urCollIotaL

end LeanFormal.IUT.XiFPaper.Mzk1URCollectionLayerActual
end