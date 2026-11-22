/- R1 assembly: q-mass endpoint + root lattice hull inclusion (no hW, no localCompletionDegree). -/
import tmp.sheaf.xif.paper.Mzk1ULR0QMEndpointActual
import tmp.sheaf.xif.paper.Mzk1G1F2JbRootMassRouteActual
import tmp.sheaf.xif.paper.Mzk1ULR1CPrimeFiberActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR1RootHullAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1ULQbVecActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR0FullFiberActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR0FiberCrosswalkActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR0RealDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR0QMEndpointActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR1CPrimeFiberActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F2JbRootMassRouteActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]

/-- R1 assembly: weighted q-mass endpoint and all root lattices J_b inside the paper Theta hull. -/
theorem rootHull_assembly
    (nuJ w logp : Bad (nativePlaceSelection T) → Real)
    (oneLabel : Bad (nativePlaceSelection T) → SignedLabel l.value)
    (hν : ∀ b, nuJ b = - cP T b * logp b)
    (hw : ∀ b, w b = thetaLamWeight T b / (2 * (l.value : Real)))
    (hcross : ∀ b, cPFullFiber T b =
      thetaLamWeight T b * cP T b)
    (hQb : ∀ b, Qb (T := T) b = cPFullFiber T b * logp b) :
    (∑ b : Bad (nativePlaceSelection T), w b * nuJ b) = - M_paper_v2 T ∧
    (∀ b : Bad (nativePlaceSelection T),
      rootLatticeJ T b (oneLabel b) ⊆ rootNormHull T b) := by
  refine ⟨sum_weight_nu_eq_neg_Mpaper (T := T) nuJ w logp hν hw hcross hQb, ?_⟩
  intro b
  exact rootLatticeJ_subset_rootNormHull T b (oneLabel b)

#print axioms rootHull_assembly

end LeanFormal.IUT.XiFPaper.Mzk1ULR1RootHullAssemblyActual