import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import LeanFormal.IUT.IUTII.Theta.EtaleThetaQuotient
import LeanFormal.IUT.IUTI.HodgeTheater.ConcreteHodgeTheaterExample
import tmp.sheaf.xif.paper.Mzk1Example36EtThCorrespondenceActual
import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual

/-!
# Mzk1IUTSkeletonCarriersActual — cross-region carrier bundle for the iut-skeleton DEF
nodes, built ONLY from existing repo assets (Lead A475 reuse rule)

Existing assets reused (all have oleans at this revision):
* LeanFormal/IUT/IUTII/Kummer/SourceLogShellCarrier.lean (SourceLogShellDatum);
* LeanFormal/IUT/IUTII/Theta/EtaleThetaQuotient.lean (ThetaQuotient/EllipticAbelianization);
* LeanFormal/IUT/IUTI/HodgeTheater/ConcreteHodgeTheaterExample.lean (gaussianHodgeTheater);
* tmp/sheaf/xif/paper/Mzk1Example36EtThCorrespondenceActual.lean (Example36 correspondence);
* tmp/sheaf/xif/paper/AbsTopIII05Section0ObjectsActual.lean (oriented graph / Frobenius picture).

This file only bundles the existing carrier types for the iut-skeleton DEF nodes
(LogShell/Thetas/HodgeTheater/Gaussian/InitialTheta/Frobenioid/HDD/PrimeStrips/ClassB); it
introduces no new theory and claims no paper statement.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTSkeletonCarriersActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Example36EtThCorrespondenceActual
open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual

/-- Carrier bundle for the iut-skeleton DEF nodes, assembled from existing repo assets. -/
structure IUTSkeletonCarriers where
  /-- LogShell node carrier (SourceLogShellDatum, universe 0 instance). -/
  logShellCarrier : Type 1
  /-- Thetas/Kummer node carrier: etale theta quotient for a group. -/
  thetaQuotientCarrier : (G : Type) → [Group G] → Type
  /-- elliptic abelianization carrier. -/
  ellipticAbelianizationCarrier : (G : Type) → [Group G] → Type
  /-- HodgeTheater/Gaussian node carrier: the concrete Gaussian Hodge theater. -/
  gaussianHodgeTheaterCarrier : (l : PrimeGeFive) → HodgeTheater l RationalPrimePlace
  /-- Frobenioid/EtTh node carrier: the Example36<->EtTh correspondence bundle. -/
  example36Correspondence : (l : PrimeGeFive) → Example36EtThCorrespondence l
  /-- HDD/Frobenius-picture node carrier: the Section-0 oriented graph Gamma. -/
  frobeniusPicture : OrientedGraph.{0}

/-- The skeleton carrier bundle is inhabited by the existing assets. -/
def iutSkeletonCarriers : IUTSkeletonCarriers where
  logShellCarrier := SourceLogShellDatum.{0}
  thetaQuotientCarrier := fun (G : Type) [Group G] => ThetaQuotient G
  ellipticAbelianizationCarrier := fun (G : Type) [Group G] => EllipticAbelianization G
  gaussianHodgeTheaterCarrier := gaussianHodgeTheater
  example36Correspondence := example36EtThCorrespondence
  frobeniusPicture := frobeniusPictureGraph

/-- The skeleton carrier bundle is nonempty. -/
theorem iutSkeletonCarriers_nonempty : Nonempty IUTSkeletonCarriers :=
  ⟨iutSkeletonCarriers⟩

/-- Skeleton reuse rows: (skeleton node, existing asset, status). -/
def iutSkeletonReuseRows : List (String × String × String) :=
  [ ("LogShell", "SourceLogShellDatum (SourceLogShellCarrier.lean)", "REUSE (tree olean)"),
    ("Thetas/Kummer", "ThetaQuotient/EllipticAbelianization (EtaleThetaQuotient.lean)", "REUSE (tree olean)"),
    ("HodgeTheater/Gaussian", "gaussianHodgeTheater (ConcreteHodgeTheaterExample.lean)", "REUSE (tree olean)"),
    ("Frobenioid/ClassB", "Example36EtThCorrespondence (Mzk1Example36EtThCorrespondenceActual)", "REUSE (EXIT0/CITABLE)"),
    ("HDD", "frobeniusPictureGraph (AbsTopIII05Section0ObjectsActual)", "REUSE (EXIT0)"),
    ("InitialTheta", "SourceInitialThetaData (tree; not re-imported here)", "REUSE anchor"),
    ("PrimeStrips", "PrimeStripsConstruction/PrimeStripFrobenioidCategorySkeleton (tree; anchor)", "REUSE anchor"),
    ("Gaussian", "Foundations/Theta Gaussian assets (tree; anchor)", "REUSE anchor") ]

/-- The skeleton reuse row record has eight rows. -/
theorem iutSkeletonReuseRows_length : iutSkeletonReuseRows.length = 8 := rfl

#check IUTSkeletonCarriers
#check iutSkeletonCarriers
#check iutSkeletonCarriers_nonempty
#check iutSkeletonReuseRows_length

end LeanFormal.IUT.XiFPaper.Mzk1IUTSkeletonCarriersActual
end
