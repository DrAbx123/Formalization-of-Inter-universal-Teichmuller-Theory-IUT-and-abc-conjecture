import tmp.sheaf.xif.paper.S3123UnitCompExplicitActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S3123XKStackExtension
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceActual
open LeanFormal.IUT.XiFPaper.S3123FiberNatTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransInvActual
open LeanFormal.IUT.XiFPaper.S3123LeftCoeActual
open LeanFormal.IUT.XiFPaper.S3123LeftExplicitActual
open LeanFormal.IUT.XiFPaper.S3123UnitCompExplicitActual

namespace LeanFormal.IUT.XiFPaper.S3123UnitAppExplicitActual

variable {l : PrimeGeFive}

/-- Statement only: the explicit-host unit component type.  The proof term was
removed because `NatIso.ofComponents` elaboration hit a kernel deterministic
timeout; the UnitIso chain uses `S3123UnitIsoDataOld` (via `S3123UnitComp`)
instead and does not consume this definition. -/
abbrev S3123UnitAppExplicitType
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) : Type :=
  (𝟙 (S3123LeftObj (l := l) U)) ≅
    (S3123FiberAppExplicit (l := l) U ≫
      S3123FiberAppInvExplicit (l := l) U)

#check S3123UnitAppExplicitType

end LeanFormal.IUT.XiFPaper.S3123UnitAppExplicitActual
end
