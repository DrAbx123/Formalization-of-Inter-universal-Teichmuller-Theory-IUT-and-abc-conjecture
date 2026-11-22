import tmp.sheaf.xif.paper.S2072HasQuotientsActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineFixedPointDescNormalForm

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2087Probe1

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientCoverProjection
open LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectAffineQuotientCoverEntry
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
open ABCBridge.AffineBaseFiniteEtaleQuotients
open ABCBridge.CoverSectionsAction
open ABCBridge.AffineQuotientUniversalProperty
open LeanFormal.IUT.XiFPaper.S2072HasQuotientsActual

universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [Finite G]
variable (F : SingleObj G ⥤ FiniteEtaleCover (Spec (CommRingCat.of R)))

section Inst

local instance instFintype : Fintype G := Fintype.ofFinite G
local instance instDecEq : DecidableEq G := Classical.decEq G
local instance instAlg : Algebra R Γ((F.obj (SingleObj.star G)).carrier, ⊤) :=
  finiteEtaleCoverSectionsAlgebra R (F.obj (SingleObj.star G))
local instance instAct : MulSemiringAction G Γ((F.obj (SingleObj.star G)).carrier, ⊤) :=
  coverSectionsMulSemiringAction (F.obj (SingleObj.star G)) (actionOfDiagram F)
local instance instSMul : SMulCommClass G R Γ((F.obj (SingleObj.star G)).carrier, ⊤) :=
  coverSectionsSMulCommClass (F.obj (SingleObj.star G)) (actionOfDiagram F)
local instance instEt : Algebra.Etale R Γ((F.obj (SingleObj.star G)).carrier, ⊤) :=
  finiteEtaleCoverSections_etale (F.obj (SingleObj.star G))
local instance instFin : Module.Finite R Γ((F.obj (SingleObj.star G)).carrier, ⊤) :=
  finiteEtaleCoverSections_finite (F.obj (SingleObj.star G))

example : (quotientCoverOfDiagram (R := R) (G := G) F).carrier =
    Spec (CommRingCat.of (fixedPointSubalgebra R Γ((F.obj (SingleObj.star G)).carrier, ⊤) G)) := rfl

example : (quotientCoverOfDiagram (R := R) (G := G) F).structureMap =
    Spec.map (CommRingCat.ofHom (algebraMap R (fixedPointSubalgebra R Γ((F.obj (SingleObj.star G)).carrier, ⊤) G))) := rfl

example : ((FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R))).map
    (quotientProjectionOfDiagram (R := R) (G := G) F)).left =
    (F.obj (SingleObj.star G)).carrier.isoSpec.hom ≫
      affineFixedPointQuotientMap R Γ((F.obj (SingleObj.star G)).carrier, ⊤) G := rfl

end Inst

end LeanFormal.IUT.XiFPaper.S2087Probe1
