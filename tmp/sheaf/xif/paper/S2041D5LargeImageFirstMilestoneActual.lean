import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual
import tmp.sheaf.xif.paper.S2009DicksonActual
import tmp.sheaf.xif.paper.S2014DicksonClassificationActual
import tmp.sheaf.xif.paper.S1993D5FiniteGroupBridgeActual
import tmp.sheaf.xif.paper.S1999S1993BridgeActual
import tmp.sheaf.xif.paper.S2005FprimeGroupActual
import tmp.sheaf.xif.paper.S2055DicksonClassActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2041D5LargeImageFirstMilestoneActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1993D5FiniteGroupBridgeActual
open LeanFormal.IUT.XiFPaper.S1999S1993BridgeActual
open LeanFormal.IUT.XiFPaper.S2005FprimeGroupActual
open LeanFormal.IUT.XiFPaper.S2055DicksonClassActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual

/-- The Dickson subgroup-classification component of the first milestone. -/
def S2041DicksonComponent : Prop :=
  S2009DicksonTransitiveClassification

/-- The finite group computations and reductions needed for the Dickson step.
Included: normalizer cardinality, transvection generation, order-five fixed
vector. -/
def S2041GroupFiniteComponents : Prop :=
  S2014NormalizerCard ∧ S2014TransvectionGeneration ∧ S2014OrderFiveUnipotent

/-- The Galois/division-field bridge components are actual (S1999/S2005). -/
theorem s2041GaloisBridgeComponents_actual :
    S1993SplittingFieldH_eq ∧ S1993FprimeGroupStructure ∧ S1993QuadraticSubfields :=
  ⟨S1999SplittingFieldH_eq, S2005FprimeGroupStructure, S2005QuadraticSubfields⟩

/-- Exact first-missing chain for the l = 5 D5 large-image input, as currently
formalized.  No inhabitant is asserted. -/
def S2041ExactFirstMissingChain : Prop :=
  S2041DicksonComponent ∧ S2041GroupFiniteComponents


/-- Dickson classification and all three S2014 components are actual (S2055). -/
theorem s2041DicksonAndGroupComponents_actual :
    S2041DicksonComponent ∧ S2014NormalizerCard ∧
      S2014TransvectionGeneration ∧ S2014OrderFiveUnipotent :=
  ⟨S2055DicksonTransitiveClassification, S2055NormalizerCard,
    S2055TransvectionGeneration, S2055OrderFiveUnipotent⟩

/-- The exact first-missing chain of S2041 is actual as a conjunction; the only
remaining mathematical input is the psi5 roots/pairs/Dedekind/Galois bridge,
which is not encoded as a hypothesis of this file. -/
theorem s2041ExactFirstMissingChain_actual :
    S2041ExactFirstMissingChain :=
  ⟨S2055DicksonTransitiveClassification,
    ⟨S2055NormalizerCard, S2055TransvectionGeneration,
      S2055OrderFiveUnipotent⟩⟩

/-- Actual consumer: a full mod-5 range at one actual basis gives the S1987
large-image target. -/
theorem s2041Target_of_fullRange
    (b : S1725TorsionBasis S1987Five)
    (h : (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range = ⊤) :
    S1987D5LargeImageFive :=
  S1987D5LargeImageFive_of_fullRange b h

/-- Actual Dickson consumer: a subgroup with surjective determinant, transitive
twelve-pair action and an element of cycle type `(10,2)` is the whole group. -/
theorem s2041SubgroupTop_of_dickson
    (hD : S2041DicksonComponent) (H : Subgroup GL2)
    (hdet : DetSurjectiveOn H) (htrans : PairTransitive H)
    (h102 : HasCycleType102 H) : H = ⊤ :=
  largeImage_of_dickson hD H hdet htrans h102

/-- If the actual mod-5 range is a subgroup satisfying the Dickson hypotheses,
then it is the whole group. -/
theorem s2041RangeTop_of_dickson
    (hD : S2041DicksonComponent)
    (b : S1725TorsionBasis S1987Five)
    (hdet : DetSurjectiveOn
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range)
    (htrans : PairTransitive
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range)
    (h102 : HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range) :
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range = ⊤ :=
  s2041SubgroupTop_of_dickson hD _ hdet htrans h102

/-- The actual range hypotheses at one basis: determinant surjective,
twelve-pair transitive and an element of cycle type (10,2). -/
def S2041RangeHypotheses (b : S1725TorsionBasis S1987Five) : Prop :=
  DetSurjectiveOn
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range ∧
    PairTransitive
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range ∧
    HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range

/-- Dickson (now actual) plus the actual range hypotheses gives range = top. -/
theorem s2041RangeTop_of_rangeHypotheses
    (b : S1725TorsionBasis S1987Five)
    (h : S2041RangeHypotheses b) :
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range = ⊤ := by
  rcases h with ⟨hdet, htrans, h102⟩
  exact s2041SubgroupTop_of_dickson S2055DicksonTransitiveClassification _ hdet htrans h102

/-- Final assembly from the actual range hypotheses. -/
theorem s2041Target_of_rangeHypotheses
    (b : S1725TorsionBasis S1987Five)
    (h : S2041RangeHypotheses b) :
    S1987D5LargeImageFive :=
  s2041Target_of_fullRange b (s2041RangeTop_of_rangeHypotheses b h)


/-- The remaining psi5/Galois/Dedekind bridge, now the only mathematical input
outside the actual Dickson/S2014 and S1999/S2005 components. -/
def S2041Psi5Remaining : Prop :=
  Nonempty S2057Mod29FactorizationData ∧
    Nonempty S2057FrobMod29CycleTypeBridge

end LeanFormal.IUT.XiFPaper.S2041D5LargeImageFirstMilestoneActual

end
