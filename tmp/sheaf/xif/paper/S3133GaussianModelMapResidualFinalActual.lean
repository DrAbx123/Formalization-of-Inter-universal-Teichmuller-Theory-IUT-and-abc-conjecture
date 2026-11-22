import tmp.sheaf.xif.paper.S3133M2aClosedActual
import tmp.sheaf.xif.paper.S3133M2bClauseBDescentActual
import tmp.sheaf.xif.paper.S3133GaussianM2MissingActual
import tmp.sheaf.xif.paper.S3133S3131GaussianModelMapMinimalActual
import tmp.sheaf.xif.paper.S3133S3131GaussianModelComponentsActual

/-!
# Final R1 minimal residual: M1 + M2b only (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: lattice S3137 R1 registry,
mainline FINAL-STATUS/registry, stage4/stepxi.

With M2a CLOSED (S3133M2aClosedActual.S3133GaussianCanonicalQNorm_holds, proved
via Mathlib valuedAdicCompletion_eq_valuation' + lattice S3137M2aToolActual +
the actual absNorm=5), the minimal Gaussian model-map residual is only:

* M1: the bad <-> all-place index equivalence with place-compatible transport
  (genuine source placeToMod provenance; contract-separated);
* M2b: the clause-B/Tate q descent (paper chosen q_v, D4).

M0 and M3 are PROVED (S3133S3131GaussianModelComponentsActual).  The old
residual structure S3133GaussianModelMapResidualMinimal is superseded: with M2a
proved, its M2 field is equivalent to M2b
(S3133GaussianQParameterMatchAtBase_iff_clauseB below).

No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3133GaussianModelMapResidualFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelComponentsActual
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelMapMinimalActual
open LeanFormal.IUT.XiFPaper.C3GaussianThetaPacketActual
open LeanFormal.IUT.XiFPaper.S3133GaussianM2MissingActual
open LeanFormal.IUT.XiFPaper.S3133M2bClauseBDescentActual
open LeanFormal.IUT.XiFPaper.S3133M2aClosedActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}

/-- Final minimal Gaussian model-map residual: only M1 and M2b. -/
structure S3133GaussianModelMapResidualFinal
    (D : SourcePilotRegionDonors I) where
  /-- actual SourceCompletion above the Gaussian model arithmetic (M0 supply) -/
  C : SourceCompletion.{0} l
  arithmetic_eq : C.arithmetic = concreteGaussianInitialThetaArithmeticData l
  /-- M1 exact residual: bad <-> all-place index equivalence + place-compatible
  transport (genuine source placeToMod provenance; contract-separated) -/
  m1_indexInjection : Prop
  /-- M2b exact residual: clause-B/Tate q descent (paper chosen q_v, D4) -/
  m2b_clauseB : Prop
  m2b_clauseB_eq :
    m2b_clauseB = S3133GaussianClauseBDescent C.toSourceNativeInitialThetaData

/-- The remaining residual is exactly M1 and M2b. -/
def S3133GaussianModelMapRemainingFinal
    (D : SourcePilotRegionDonors I)
    (R : S3133GaussianModelMapResidualFinal D) : Prop :=
  R.m1_indexInjection ∧ R.m2b_clauseB

/-- M0 is PROVED from the supplied actual SourceCompletion. -/
theorem S3133GaussianModelMapResidualFinal_m0
    (D : SourcePilotRegionDonors I)
    (R : S3133GaussianModelMapResidualFinal D) :
    S3133GaussianModelArithmeticMatch R.C.toSourceNativeInitialThetaData :=
  S3133GaussianModelArithmeticMatch_of_completion R.C R.arithmetic_eq

/-- M3 is PROVED for the actual Gaussian Stage-2 image from the donors. -/
theorem S3133GaussianModelMapResidualFinal_m3
    (D : SourcePilotRegionDonors I) :
    S3133GaussianThetaValueMatch (actualGaussianC3 D) :=
  S3133GaussianThetaValueMatch_actualGaussian (l := l) (V := V) (I := I) D

/-- The old (M1 + shrunk M2) residual converts to the final residual: M2a is
proved, so only M2b remains. -/
noncomputable def S3133GaussianModelMapResidualFinal_of_minimal
    (D : SourcePilotRegionDonors I)
    (R : S3133GaussianModelMapResidualMinimal (l := l) (V := V) (I := I) D) :
    S3133GaussianModelMapResidualFinal D :=
  { C := R.C
    arithmetic_eq := R.arithmetic_eq
    m1_indexInjection := R.m1_indexInjection
    m2b_clauseB := S3133GaussianClauseBDescent R.C.toSourceNativeInitialThetaData
    m2b_clauseB_eq := rfl }

/-- With M2a proved, the old shrunk-M2 residual field is equivalent to M2b. -/
theorem S3133GaussianQParameterMatchAtBase_iff_clauseB
    (T : SourceNativeInitialThetaData.{0} l) :
    S3133GaussianQParameterMatchAtBase T ↔ S3133GaussianClauseBDescent T :=
  ⟨S3133GaussianClauseBDescent_of_atBase T,
    fun h => S3133GaussianQParameterMatchAtBase_of_ClauseBDescent_and_canonicalQ
      T S3133GaussianCanonicalQNorm_holds h⟩

/-- Final R1 interface: M0 and M3 PROVED; residual exactly M1 and M2b. -/
theorem S3137R1_interface_final
    (D : SourcePilotRegionDonors I)
    (R : S3133GaussianModelMapResidualFinal D) :
    S3133GaussianModelArithmeticMatch R.C.toSourceNativeInitialThetaData ∧
      S3133GaussianThetaValueMatch (actualGaussianC3 D) ∧
      (R.m1_indexInjection ∧ R.m2b_clauseB ↔
        S3133GaussianModelMapRemainingFinal D R) :=
  ⟨S3133GaussianModelMapResidualFinal_m0 D R,
    S3133GaussianModelMapResidualFinal_m3 D,
    Iff.rfl⟩

end LeanFormal.IUT.XiFPaper.S3133GaussianModelMapResidualFinalActual
