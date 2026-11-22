import tmp.sheaf.xif.paper.S995FiniteCarrierCor312ConclusionActual
import tmp.sheaf.xif.paper.S919GlobalWeightedInequalityActual

/-! # S1000: final Cor312 assembly

S995 is the actual finite-carrier Cor312 theorem.  S996-S999 are not present in
the tree as separate files, so S1000 bundles exactly the S995 inputs:
S994FiniteInput, a PaperXiFSourceLink, its link_identification proof, and the
finite link evidence.  The conclusion is the actual per-b inequality, weighted
inequality, and Cor312Conclusion.  Only inequalities, no equality/scaling data.
The exact minimal condition is S1000FinalInputRequired. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1000FinalCor312AssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S995FiniteCarrierCor312ConclusionActual
open LeanFormal.IUT.XiFPaper.S968FinalTensorInequalityCor312Actual
open LeanFormal.IUT.XiFPaper.S983PaperXiFSourceLinkConstructionActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open MeasureTheory

universe ua uv upi umon ui uL uC uG uX uLabel u uC3 uD3 uM uP
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G' : Type uG} [Group G'] [TopologicalSpace G']
variable {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable (O : PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
  (Label := Label) (Choice := Choice) (I := I) G' envStrip)
variable (C3 : SourcePilotRegionData (V := FinitePrimePlace 2 7) I)

/-- Exact bundled S995 inputs. -/
structure S1000FinalInputs where
  In : S994FiniteInput T
  link : PaperXiFSourceLink O P C3
  hlink : link.link_identification
  links : FiniteStepXILinkEvidence
    (paperCertificate (I := paperXiFInput
      (s968Inclusion (l := l) (V := FinitePrimePlace 2 7)
        (Label := Label) (Choice := Choice) (G' := G') (envStrip := envStrip)
        P O C3 link hlink))).toStepXIFiniteCertificate

/-- Final actual assembly: per-b inequality, weighted inequality, Cor312. -/
theorem s1000FinalCor312
    (D : S1000FinalInputs (l := l) (I := I)
      (T := T) P O C3) :
    (∀ b : Bad (nativePlaceSelection T),
      s994VR T D.In b ≤ s994VS T D.In b) ∧
      weightedPaperV T (s994VR T D.In) ≤
        weightedPaperV T (s994VS T D.In) ∧
      Cor312Conclusion
        ((paperCertificate (I := paperXiFInput
          (s968Inclusion (l := l) (V := FinitePrimePlace 2 7)
            (Label := Label) (Choice := Choice) (G' := G') (envStrip := envStrip)
            P O C3 D.link D.hlink))).toContract
          (paperSignedLinkEvidence
            (I := paperXiFInput
              (s968Inclusion (l := l) (V := FinitePrimePlace 2 7)
                (Label := Label) (Choice := Choice) (G' := G') (envStrip := envStrip)
                P O C3 D.link D.hlink)) D.links)) := by
  exact s995FiniteCarrierCor312Conclusion (l := l) (T := T) (P := P) (O := O) (C3 := C3)
    D.In D.link D.hlink D.links

/-- Projection of the actual final assembly: only the Cor312Conclusion component.
Mathematically identical to the third conjunct of s1000FinalCor312. -/
theorem s1000Cor312Conclusion
    (D : S1000FinalInputs (l := l) (I := I)
      (T := T) P O C3) :
    Cor312Conclusion
      ((paperCertificate (I := paperXiFInput
        (s968Inclusion (l := l) (V := FinitePrimePlace 2 7)
          (Label := Label) (Choice := Choice) (G' := G') (envStrip := envStrip)
          P O C3 D.link D.hlink))).toContract
        (paperSignedLinkEvidence
          (I := paperXiFInput
            (s968Inclusion (l := l) (V := FinitePrimePlace 2 7)
              (Label := Label) (Choice := Choice) (G' := G') (envStrip := envStrip)
              P O C3 D.link D.hlink)) D.links)) :=
  (s1000FinalCor312 (l := l) (I := I) (T := T) (P := P) (O := O) (C3 := C3) D).2.2

/-- Exact minimal condition for the final assembly. -/
def S1000FinalInputRequired : Prop :=
  Nonempty (S1000FinalInputs (l := l) (I := I)
    (T := T) P O C3)

end LeanFormal.IUT.XiFPaper.S1000FinalCor312AssemblyActual

end
