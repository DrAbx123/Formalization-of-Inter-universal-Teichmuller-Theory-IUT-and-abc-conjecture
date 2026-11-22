import tmp.sheaf.xif.paper.S3136LGPTensorOLatticeIdentificationActual
import tmp.sheaf.xif.paper.S3136LGPThetaMuQuasiLatticeActual

/-! # Stage-4 host: bad-local O-lattice / mu_{2l}-quasi-lattice component

Source anchors: IUT III, Prop. 3.2, (ii) (pp. 97--99); Prop. 3.4, (ii)
(pp. 102--103); Prop. 3.7, (ii), (v) (pp. 108--112).

Conditional on the bad<->C3 index equivalence, this file bundles the actual
local data of the bad packet fibers that the paper's local tensor packet needs:
* lgpBadLocalQuasiLattice e b: the actual O-lattice (integral log-shell
  subgroup) of the fiber, the actual mu_{2l} subgroup of the unit group, the
  actual theta classes, and their construction equalities;
* actual inhabitant and projection theorems;
* LGPBadLocalQuasiLatticeMissing/Gap: exact missing data (embedding of the
  theta unit subgroup into the IQ packet, O-lattice compatibility, rho_lgp,v).

LABEL: prerequisite component only.  Consumer: lattice stream,
IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPLocalOLatticeQuasiLatticeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.LGPThetaActionActual
open LeanFormal.IUT.XiFPaper.PaperSymbolTypesActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
open LeanFormal.IUT.XiFPaper.S3136LGPLocalMonoidActual
open LeanFormal.IUT.XiFPaper.S3136LGPLocalTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3136LGPJvPacketTransportActual
open LeanFormal.IUT.XiFPaper.S3136LGPTensorOLatticeIdentificationActual
open LeanFormal.IUT.XiFPaper.S3136LGPXMuUnitActual
open LeanFormal.IUT.XiFPaper.S3136LGPThetaMuQuasiLatticeActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Bundled actual local O-lattice / mu_{2l}-quasi-lattice data at a bad packet
fiber. -/
structure LGPBadLocalQuasiLattice
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (b : Bad (nativePlaceSelection T)) where
  /-- The actual O-lattice of the packet fiber. -/
  olattice : AddSubgroup (lgpBadLocalPacketFiber T C3 e b)
  olattice_eq : olattice = lgpLocalOLattice T C3 e b
  olattice_coe :
    ((olattice : AddSubgroup (lgpBadLocalPacketFiber T C3 e b)) :
        Set (lgpBadLocalPacketFiber T C3 e b)) =
      lgpBadLocalPacketRegion T C3 e b
  /-- The actual mu_{2l} subgroup of the actual unit group. -/
  muSubgroup : Subgroup (AlgebraicClosure (Completion (qVPlace T b)))ˣ
  muSubgroup_eq : muSubgroup = muTwoLAlgClosedSubgroup T b
  /-- The actual theta-value classes in the mu_{2l}-quotient. -/
  thetaClass : LGPThetaIndex l →
    (AlgebraicClosure (Completion (qVPlace T b)))ˣ ⧸
      muTwoLAlgClosedSubgroup T b
  thetaClass_eq : ∀ j, thetaClass j = lgpThetaValueQuotient T b j

/-- The actual local O-lattice / mu_{2l}-quasi-lattice component. -/
noncomputable def lgpBadLocalQuasiLattice
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (b : Bad (nativePlaceSelection T)) :
    LGPBadLocalQuasiLattice T C3 e b where
  olattice := lgpLocalOLattice T C3 e b
  olattice_eq := rfl
  olattice_coe := lgpLocalOLattice_coe T C3 e b
  muSubgroup := muTwoLAlgClosedSubgroup T b
  muSubgroup_eq := rfl
  thetaClass := lgpThetaValueQuotient T b
  thetaClass_eq := fun _ => rfl

/-- Exact missing data at the local O-lattice/quasi-lattice layer (IUT III,
Prop. 3.2, (ii), pp. 97--99; Prop. 3.4, (ii), pp. 102--103; Prop. 3.7,
(ii), (v), pp. 108--112):
* unitSubgroupEmbedding: embedding of the theta-value unit subgroup into the
  IQ packet;
* olatticeCompatibility: the O-lattice tensor identification;
* muQuasiLatticeCompatibility: compatibility of the mu_{2l}-classes with the
  packet label components;
* rhoLgpCompat: compatibility with rho_lgp,v. -/
structure LGPBadLocalQuasiLatticeMissing where
  unitSubgroupEmbedding : Prop
  olatticeCompatibility : Prop
  muQuasiLatticeCompatibility : Prop
  rhoLgpCompat : Prop

/-- The exact local quasi-lattice gap. -/
def LGPBadLocalQuasiLatticeGap : Prop :=
  Nonempty LGPBadLocalQuasiLatticeMissing

#check lgpBadLocalQuasiLattice
#check LGPBadLocalQuasiLatticeGap

end LeanFormal.IUT.XiFPaper.S3136LGPLocalOLatticeQuasiLatticeActual
end