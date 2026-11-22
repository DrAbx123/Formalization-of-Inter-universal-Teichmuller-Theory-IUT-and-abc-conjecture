import tmp.sheaf.xif.paper.S1964QuotientCFActual
import tmp.sheaf.xif.paper.S1971ActionStackificationActual
import tmp.sheaf.xif.paper.S1983EtThSignatureBridgeActual
import tmp.sheaf.xif.paper.S1989KSideCoverActual
import tmp.sheaf.xif.paper.S1994KSideCoversActual
import tmp.sheaf.xif.paper.S1881D9D7bActual
import tmp.sheaf.xif.paper.S2022QuotientStackActual
import tmp.sheaf.s1984.S1984KSideObjectAudit

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2043D9FullActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1964QuotientCFActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S1983EtThSignatureBridgeActual
open LeanFormal.IUT.XiFPaper.S1881D9D7bActual
open LeanFormal.IUT.XiFPaper.S1994KSideCovers
open LeanFormal.IUT.XiFPaper.S1989KSideCover
open LeanFormal.IUT.XiFPaper.S1984KSideObjectAudit
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.InitialThetaSource

universe u

/-- C_F exact first missing at the quotient-stack level: a functorial
pointwise quotient colimit that is an actual etale stack.  The pointwise
action groupoid alone is not this object. -/
def S2043CFQuotientStackFirstMissing : Prop :=
  S1971QuotientStack

/-- C_F exact first missing witness form: an actual hyperbolic quotient
orbicurve whose fibers are the pointwise sign quotient, with sign-invariant
quotient morphism and bicategorical universal property. -/
def S2043CFStackWitnessFirstMissing
    (l : PrimeGeFive) (A : Iut.OrbicurveSignAction S1726Orbicurve) : Prop :=
  Nonempty (S1971StackQuotientWitness l A)

/-- C_F honest [EtTh] target: the quotient with the honest signature
(0; [2,2,2]; 1), not the paper's (1,1)^pm label. -/
def S2043CFHonestFirstMissing
    (l : PrimeGeFive) (A : Iut.OrbicurveSignAction S1726Orbicurve) : Prop :=
  S1983FirstMissing l A

/-- K-side exact first missing: an actual orbicurve over K with an order-l
stacky point (the l-tors root orbicurve). -/
def S2043KSideFirstMissing
    (l : PrimeGeFive) (A : InitialThetaArithmeticData l) : Prop :=
  S1994StackyOrbicurveMissing l A

/-- K-side paper cover first missing: the full degree-l cover record with
honest stacky points over the production core. -/
def S2043KSideCoverFirstMissing
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : S1984PaperKCore l A S} : Prop :=
  S1994PaperKSideCoverMissing l A S C

/-- D9 orbicurve slot first missing, as recorded by S1881. -/
def S2043D9SlotFirstMissing (l : PrimeGeFive) : Prop :=
  S1881D9OrbicurveMissing l

/-- The actual honest C_F signature is (0; [2,2,2]; 1). -/
theorem S2043paperCF_signature :
    etthSignature paperCFType = S1964HonestQuotientSignature :=
  paperCF_signature

/-- A stack quotient witness gives the S1964 quotient structure. -/
theorem S2043S1964Quotient_of_stackWitness
    {l : PrimeGeFive} {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (h : S2043CFStackWitnessFirstMissing l A) :
    S1964FirstMissing l A :=
  S1964FirstMissing_ofStackQuotientWitness h

/-- Honest C_F target gives the S1964 quotient structure. -/
theorem S2043S1964Quotient_of_honestMissing
    {l : PrimeGeFive} {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (h : S2043CFHonestFirstMissing l A) :
    S1964FirstMissing l A :=
  S1964FirstMissing_ofS1983 h

/-- K-side stacky orbicurve missing is the geometric first field for the
K-side degree-l cover. -/
theorem S2043KSideStacky_of_coverMissing
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : S1984PaperKCore l A S}
    (h : S2043KSideCoverFirstMissing (A := A) (S := S) (C := C)) :
    S2043KSideFirstMissing l A :=
  S1994stackyOrbicurveMissing_of_paper h

#print axioms S2043paperCF_signature
#print axioms S2043S1964Quotient_of_stackWitness
#print axioms S2043S1964Quotient_of_honestMissing
#print axioms S2043KSideStacky_of_coverMissing

end LeanFormal.IUT.XiFPaper.S2043D9FullActual

end
