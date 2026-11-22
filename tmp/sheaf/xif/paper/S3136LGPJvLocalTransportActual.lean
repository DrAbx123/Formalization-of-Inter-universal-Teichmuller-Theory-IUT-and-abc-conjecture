import tmp.sheaf.xif.paper.S3136LGPJvPacketTransportActual

/-! # Stage-4 host: local J_v generator transport (Z-power of the 2l-th root)

Source anchors: IUT III, Prop. 3.7, (ii), (v) (pp. 108--112); IUT III,
Prop. 3.2, (ii) (pp. 97--99).

This file constructs the actual local generator transport of the candidate
fractional ideal:
* lgpRootZPowerHom b: the Z-indexed generator map m |-> root^m of the actual
  2l-th root, as a monoid homomorphism from Multiplicative Z to the actual unit
  group;
* lgpRootZPowerHom_mem_thetaValueSubgroup: its image lies in the actual
  theta-value subgroup (the unit-side J_v candidate);
* lgpRootZPowerHom_twoL: the exponent (2l) maps to the actual q_v unit (the
  principal q_v compatibility);
* LGPJvLocalTransportMissing/Gap: exact missing data (embedding into the IQ
  packet, O-lattice compatibility, mu_{2l}-quasi-lattice, rho_lgp,v).

LABEL: prerequisite component only.  Consumer: lattice stream,
IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPJvLocalTransportActual

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
open LeanFormal.IUT.XiFPaper.S3136LGPJvPacketTransportActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The Z-indexed generator map of the actual 2l-th root: m |-> root^m. -/
noncomputable def lgpRootZPowerHom (b : Bad (nativePlaceSelection T)) :
    Multiplicative ℤ →* (AlgebraicClosure (Completion (qVPlace T b)))ˣ where
  toFun m := (hodgeTwoLthRoot T b) ^ m.toAdd
  map_one' := by simp
  map_mul' m n := by rw [toAdd_mul, zpow_add]

/-- The generator map lands in the actual theta-value subgroup. -/
theorem lgpRootZPowerHom_mem_thetaValueSubgroup
    (b : Bad (nativePlaceSelection T)) (m : Multiplicative ℤ) :
    lgpRootZPowerHom T b m ∈ lgpThetaValueSubgroup T b := by
  unfold lgpRootZPowerHom
  exact Subgroup.zpow_mem (lgpThetaValueSubgroup T b)
    (lgpRoot_mem_thetaValueSubgroup T b) m.toAdd

/-- The exponent 2l maps to the actual q_v unit: the principal q_v
compatibility of the local generator transport. -/
theorem lgpRootZPowerHom_twoL (b : Bad (nativePlaceSelection T)) :
    lgpRootZPowerHom T b (Multiplicative.ofAdd ((2 * l.value : ℕ) : ℤ)) =
      qVAlgClosedUnit T b := by
  unfold lgpRootZPowerHom
  change (hodgeTwoLthRoot T b) ^ ((2 * l.value : ℕ) : ℤ) = qVAlgClosedUnit T b
  rw [zpow_natCast, hodgeTwoLthRoot_pow]

/-- Exact missing data for the local J_v generator transport (IUT III,
Prop. 3.2, (ii), pp. 97--99; Prop. 3.7, (ii), (v), pp. 108--112):
* iqPacketEmbedding: the embedding of the generated unit subgroup into the
  actual local tensor packet IQ(A,alpha Fv);
* oLatticeCompatibility: compatibility with the actual O-lattice of the packet;
* muQuasiLattice: the mu_{2l}-quasi-lattice identification;
* rhoLgpCompat: compatibility with rho_lgp,v. -/
structure LGPJvLocalTransportMissing where
  iqPacketEmbedding : Prop
  oLatticeCompatibility : Prop
  muQuasiLattice : Prop
  rhoLgpCompat : Prop

/-- The exact local J_v transport gap. -/
def LGPJvLocalTransportGap : Prop := Nonempty LGPJvLocalTransportMissing

#check lgpRootZPowerHom
#check lgpRootZPowerHom_mem_thetaValueSubgroup
#check lgpRootZPowerHom_twoL
#check LGPJvLocalTransportGap

end LeanFormal.IUT.XiFPaper.S3136LGPJvLocalTransportActual
end