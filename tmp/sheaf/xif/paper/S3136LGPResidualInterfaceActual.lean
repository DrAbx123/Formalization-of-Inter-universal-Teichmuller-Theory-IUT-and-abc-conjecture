import tmp.sheaf.xif.paper.S3136LGPXMuUnitActual
import tmp.sheaf.xif.paper.S3136LGPLocalMonoidActual
import tmp.sheaf.xif.paper.S3136LGPBadWeightNormalizationActual
import tmp.sheaf.xif.paper.S3136LGPThetaMuQuasiLatticeActual

/-! # Stage-4 host: consumer-facing LGP actual-component interface

Source anchors: IUT III, Prop. 3.4, (ii) (pp. 102--103); Prop. 3.7, (iii),
(iv) (pp. 109--111); Def. 3.8, (i), (ii) (pp. 112--113); IUT II, Remark 2.5.1,
(i); IUT III, Remark 3.9.4.

COMPONENT, not a paper object (policy §8).  This file packages the actual local
LGP components (unit layer, mu_{2l}-quotient, theta classes, bad weights, their
normalization) into one consumer-facing structure, together with the exact
Missing records for the paper-level identifications.  Named consumers: lattice
S3137 R1/R-A/R-C refinement, stepxi C2 finite copy action, mainline M4.

The actual component data:
* lgpActualComponents: bundled actual objects (phi, local monoid family, unit
  layer family, mu quotient, theta classes, bad weights, normalized weights);
* lgpActualComponents_available: the actual inhabitant;
* lgpLocalResidualInterface: the exact local residual propositions (identification
  of the local monoid, of the x mu unit portion, and of the normalization);
* lgpLocalResidualInterface_available: the bundled residual record.

LABEL: prerequisite component + residual index only.  No paper object is
claimed; no contract change; no ABC-strength content. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPResidualInterfaceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.LGPThetaActionActual
open LeanFormal.IUT.XiFPaper.PaperSymbolTypesActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
open LeanFormal.IUT.XiFPaper.S3136LGPLocalMonoidActual
open LeanFormal.IUT.XiFPaper.S3136LGPXMuUnitActual
open LeanFormal.IUT.XiFPaper.S3136LGPWeightAgreementBridgeActual
open LeanFormal.IUT.XiFPaper.S3136LGPBadWeightNormalizationActual
open LeanFormal.IUT.XiFPaper.S3136LGPThetaMuQuasiLatticeActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The bundled actual local LGP components (unit layer, mu_{2l}-quotient, theta
classes, bad weights and normalized weights). -/
structure LGPActualComponents where
  /-- The actual candidate local LGP-monoids (value + unit layers). -/
  localMonoid : ∀ b : Bad (nativePlaceSelection T), LGPLocalMonoidCandidate T b
  /-- The actual mu_{2l}-quotient unit-group candidate. -/
  xmuUnit : ∀ b : Bad (nativePlaceSelection T), LGPXMuUnitCandidate T b
  /-- The actual mu_{2l}-quasi-lattice classes of the theta values. -/
  thetaClass : ∀ b : Bad (nativePlaceSelection T),
    LGPThetaIndex l →
      (AlgebraicClosure (Completion (qVPlace T b)))ˣ ⧸
        muTwoLAlgClosedSubgroup T b
  /-- The actual bad weights (q_v divisor exponents). -/
  badWeight : Bad (nativePlaceSelection T) → ℝ
  /-- The actual normalized bad weights. -/
  normalizedWeight : Bad (nativePlaceSelection T) → ℝ

/-- The actual bundled local LGP components. -/
noncomputable def lgpActualComponents : LGPActualComponents (l := l) T where
  localMonoid := lgpLocalMonoidCandidate T
  xmuUnit := lgpXMuUnitCandidate T
  thetaClass := lgpThetaValueQuotient T
  badWeight := lgpBadWeight T
  normalizedWeight := lgpBadNormalizedWeight T

/-- The actual bundled local LGP components are available. -/
theorem lgpActualComponents_available :
    Nonempty (LGPActualComponents (l := l) T) :=
  ⟨lgpActualComponents T⟩

/-- The exact local residual propositions for the paper-level identifications
(recorded, NOT proved):
* localMonoidIdentification: for every bad place, the identification of the
  candidate local LGP-monoid with the paper Psi_FLGP,v (III Prop 3.4(ii));
* xmuUnitIdentification: for every bad place, the identification of the
  mu_{2l}-quotient candidate with the paper's x mu unit portion (III Prop
  3.7(iii)(iv), Def 3.8(i)(ii));
* badWeightNormalization: the qpilot normalization comparison and the realified
  log-volume normalization (II Rem 2.5.1(i); III Rem 3.9.4; Prop 3.9(i)). -/
structure LGPLocalResidualInterface where
  localMonoidIdentification : Prop
  xmuUnitIdentification : Prop
  badWeightNormalization : Prop

/-- The bundled local residual record; its fields are the exact Gap
propositions of the corresponding components. -/
def lgpLocalResidualInterface
    (hmono : ∀ b : Bad (nativePlaceSelection T),
      LGPLocalMonoidIdentificationGap T b)
    (hxmu : ∀ b : Bad (nativePlaceSelection T),
      LGPXMuUnitIdentificationGap T b)
    (hnorm : LGPBadWeightNormalizationGap) :
    LGPLocalResidualInterface where
  localMonoidIdentification := ∀ b : Bad (nativePlaceSelection T),
    LGPLocalMonoidIdentificationGap T b
  xmuUnitIdentification := ∀ b : Bad (nativePlaceSelection T),
    LGPXMuUnitIdentificationGap T b
  badWeightNormalization := LGPBadWeightNormalizationGap

#check lgpActualComponents
#check lgpActualComponents_available
#check LGPLocalResidualInterface
#check lgpLocalResidualInterface

end LeanFormal.IUT.XiFPaper.S3136LGPResidualInterfaceActual
end