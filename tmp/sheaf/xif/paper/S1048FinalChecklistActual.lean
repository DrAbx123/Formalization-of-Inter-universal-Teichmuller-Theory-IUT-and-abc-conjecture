import tmp.sheaf.xif.paper.S1042GlobalQParameterCardActual
import tmp.sheaf.xif.paper.S1044GlobalFiniteLinksActual

/-! # S1048: final checklist on the GLOBAL S1041 path

Removes the local sourceQ/local=global path.  The components are:
S1041 global certificate, S1042 actual global qParameter card (from nonempty
bad places), S1044 finite link evidence from IPL/SHE/APT evidence.  The only
remaining exact inputs are the global comparison hcomp, nonempty bad places,
and the IPL/SHE/APT propositions with their evidence.  S1043 is absent. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1048FinalChecklistActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S1041GlobalizedAssemblyActual
open LeanFormal.IUT.XiFPaper.S1042GlobalQParameterCardActual
open LeanFormal.IUT.XiFPaper.S1044GlobalFiniteLinksActual
open MeasureTheory

universe ua uv upi umon ui uL uC uG uX uLabel u
variable {l : PrimeGeFive}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G' : Type uG} [Group G'] [TopologicalSpace G']
variable {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable (O : PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
  (Label := Label) (Choice := Choice) (I := I) G' envStrip)

/-- Exact remaining inputs on the global path. -/
structure S1048FinalExactInputs where
  hcomp : P.procession.average ≤ -O.qPilotLogVolume
  badPlaces : Nonempty I.initial.badPlaces
  links : S1044IPLSHEAPTEvidence

/-- Final global Cor312Conclusion using actual S1042 card + S1044 finite links.
No local sourceQ / local=global bridge is used. -/
theorem s1048GlobalFinalCor312
    (X : S1048FinalExactInputs (l := l) P O) :
    Cor312Conclusion
      ((s1041GlobalCertificate (l := l) P O X.hcomp
        (s1042GlobalQParameterCard O X.badPlaces)).toContract
        (s1041GlobalSignedEvidence (l := l) P O X.hcomp
          (s1042GlobalQParameterCard O X.badPlaces)
          (s1044FiniteLinks (l := l) P O X.hcomp
            (s1042GlobalQParameterCard O X.badPlaces) X.links))) :=
  s1044GlobalFinalCor312 (l := l) P O X.hcomp
    (s1042GlobalQParameterCard O X.badPlaces) X.links

/-- Exact checklist separated from actual components. -/
structure S1048FinalExactChecklist where
  hcomp : Prop
  hcomp_eq : hcomp = (P.procession.average ≤ -O.qPilotLogVolume)
  nonemptyBadPlaces : Prop
  nonemptyBadPlaces_eq : nonemptyBadPlaces = Nonempty I.initial.badPlaces
  ipl : Prop
  she : Prop
  apt : Prop
  ipl_evidence : ipl
  she_evidence : she
  apt_evidence : apt

end LeanFormal.IUT.XiFPaper.S1048FinalChecklistActual
end