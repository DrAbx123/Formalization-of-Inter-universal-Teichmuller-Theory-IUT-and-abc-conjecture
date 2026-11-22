import tmp.sheaf.xif.paper.S3136LGPJvPacketTransportActual

/-! # Stage-4 host: tensor O-lattice identification component

Source anchors: IUT III, Prop. 3.2, (ii) (pp. 97--99): the integral structure
I(alpha D_vQ) is a tensor/direct-sum of the local log-shells I(D_v), and IQ(-)
is its Q-span; IUT III, Prop. 3.7, (ii), (v) (pp. 108--112) for the local
fractional ideals built from those lattices.

Conditional on the named bad<->C3 index equivalence, this file identifies the
TENSOR-level O-lattice data of the local packet family with the actual C3
tensor packet: tensor integral cone, IQ Q-span, family of local O-lattices and
their carrier compatibilities.  The exact tensor-product comparison with the
paper's I(alpha D_vQ) and the J_v embedding are recorded as exact missing.

LABEL: prerequisite component only.  Consumer: lattice stream,
IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPTensorOLatticeIdentificationActual

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
open LeanFormal.IUT.XiFPaper.S3136LGPLocalTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3136LGPJvPacketTransportActual
open LeanFormal.IUT.LocalFieldLogarithm

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual tensor integral region of the local log-shells (the tensor
O-lattice cone). -/
noncomputable def lgpTensorIntegralCone : Set (C3LogShellTensorBlock C3) :=
  actualC3LogShellTensorRegion C3

/-- The tensor O-lattice cone is compact (actual C3 compactness). -/
theorem lgpTensorIntegralCone_compact :
    IsCompact (lgpTensorIntegralCone C3) := by
  unfold lgpTensorIntegralCone
  exact actualC3LogShellTensorRegion_compact C3

/-- The actual Q-span of the tensor O-lattice cone (the IQ operation). -/
noncomputable def lgpTensorIntegralIQLattice :
    Submodule ℚ (C3LogShellTensorBlock C3) :=
  actualC3LogShellTensorIQ C3

/-- The tensor O-lattice cone generates the actual IQ Q-span. -/
theorem lgpTensorIntegralIQLattice_eq :
    lgpTensorIntegralIQLattice C3 =
      Submodule.span ℚ (lgpTensorIntegralCone C3) := by
  unfold lgpTensorIntegralIQLattice lgpTensorIntegralCone
  rfl

/-- The family of actual local O-lattices over the bad places. -/
noncomputable def lgpTensorOLatticeCandidate
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex) :
    ∀ b : Bad (nativePlaceSelection T),
      AddSubgroup (lgpBadLocalPacketFiber T C3 e b) :=
  fun b => lgpLocalOLattice T C3 e b

/-- The family O-lattice carrier is the compact local log-shell region. -/
theorem lgpTensorOLatticeCandidate_coe
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (b : Bad (nativePlaceSelection T)) :
    ((lgpTensorOLatticeCandidate T C3 e b :
        AddSubgroup (lgpBadLocalPacketFiber T C3 e b)) :
        Set (lgpBadLocalPacketFiber T C3 e b)) =
      lgpBadLocalPacketRegion T C3 e b := by
  exact lgpLocalOLattice_coe T C3 e b

/-- Bundled tensor O-lattice identification: tensor cone, IQ Q-span, local
O-lattice family and carrier compatibilities, all actual. -/
structure LGPTensorOLatticeIdentification
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex) where
  tensorCone : Set (C3LogShellTensorBlock C3)
  tensorCone_eq : tensorCone = lgpTensorIntegralCone C3
  tensorCone_compact : IsCompact tensorCone
  tensorIQ : Submodule ℚ (C3LogShellTensorBlock C3)
  tensorIQ_eq : tensorIQ = lgpTensorIntegralIQLattice C3
  localLattice : ∀ b : Bad (nativePlaceSelection T),
    AddSubgroup (lgpBadLocalPacketFiber T C3 e b)
  localLattice_eq : ∀ b, localLattice b = lgpLocalOLattice T C3 e b
  localLattice_coe : ∀ b,
    ((localLattice b : AddSubgroup (lgpBadLocalPacketFiber T C3 e b)) :
        Set (lgpBadLocalPacketFiber T C3 e b)) =
      lgpBadLocalPacketRegion T C3 e b

/-- The actual tensor O-lattice identification. -/
noncomputable def lgpTensorOLatticeIdentification
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex) :
    LGPTensorOLatticeIdentification T C3 e where
  tensorCone := lgpTensorIntegralCone C3
  tensorCone_eq := rfl
  tensorCone_compact := lgpTensorIntegralCone_compact C3
  tensorIQ := lgpTensorIntegralIQLattice C3
  tensorIQ_eq := rfl
  localLattice := lgpTensorOLatticeCandidate T C3 e
  localLattice_eq := fun _ => rfl
  localLattice_coe := lgpTensorOLatticeCandidate_coe T C3 e

/-- Exact identification data needed to compare the tensor O-lattice candidate
with the paper's integral structure I(alpha D_vQ) and the local fractional
ideals J_v (IUT III, Prop. 3.2, (ii), pp. 97--99; Prop. 3.7, (ii), (v),
pp. 108--112).
* tensorProductComparison: the comparison of the actual tensor cone with the
  paper's tensor/direct-sum of local log-shells (index/place comparison plus
  the tensor structure itself);
* jvEmbedding: the embedding of the J_v candidates into the IQ packet;
* muQuasiLatticeIdentification: the mu_{2l}-quasi-lattice identification of the
  theta-value generators with the paper's O-lattice;
* rhoLgpCompat: compatibility with rho_lgp,v. -/
structure LGPTensorOLatticeIdentificationMissing where
  tensorProductComparison : Prop
  jvEmbedding : Prop
  muQuasiLatticeIdentification : Prop
  rhoLgpCompat : Prop

/-- The exact tensor O-lattice identification gap. -/
def LGPTensorOLatticeIdentificationGap : Prop :=
  Nonempty LGPTensorOLatticeIdentificationMissing

#check lgpTensorIntegralCone_compact
#check lgpTensorIntegralIQLattice_eq
#check lgpTensorOLatticeCandidate_coe
#check lgpTensorOLatticeIdentification
#check LGPTensorOLatticeIdentificationGap

end LeanFormal.IUT.XiFPaper.S3136LGPTensorOLatticeIdentificationActual
end