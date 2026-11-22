import tmp.sheaf.xif.paper.Mzk1TreeHullInterfaceFactsActual
import LeanFormal/IUT/IUTIII/Corollary312/StepXI/CertificateHullWiring
import LeanFormal/IUT/IUTII/Kummer/SourceThetaPilotIQContainment

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1ConsumerChainPackageActual — A476 real consumer/chain theorems

Each declaration below combines at least two existing results into a new
conclusion (no file bookkeeping, no List String asset tables):

1. `hull_volume_package`: H5 interface facts
   (`Mzk1TreeHullInterfaceFactsActual.treeHullFacts_interface`) +
   `iqHullRealVolume_nonneg` (CertificateHullWiring.lean:93) ->
   image⊆hull ∧ 0<=realVolume ∧ logVolume<⊤;
2. `hull_realVolume_le_theta_of_logVolume`: the interface-correction
   equivalence `iqHullRealVolume_le_theta_iff` (:106) consumed backwards, so
   an ENNReal log-volume bound transfers to the real hull-volume bound;
3. `thetaPilot_iq_package`: theta-pilot generator membership
   (`SourceThetaPilotIQContainment.lean:126`) + product-map image containment
   (:141) -> both containment conclusions simultaneously.

No sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ConsumerChainPackageActual

open LeanFormal.IUT

/-- **H5 hull-volume package consumer.** -/
theorem hull_volume_package {X : Type*} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull ∧ 0 ≤ iqHullRealVolume W ∧ W.logVolume W.hull < ⊤ :=
  ⟨(LeanFormal.IUT.XiFPaper.Mzk1TreeHullInterfaceFactsActual.treeHullFacts_interface W).1,
   iqHullRealVolume_nonneg W,
   (LeanFormal.IUT.XiFPaper.Mzk1TreeHullInterfaceFactsActual.treeHullFacts_interface W).2⟩

/-- **Real hull-volume bound from an ENNReal log-volume bound** (consumer of the
interface-correction equivalence). -/
theorem hull_realVolume_le_theta_of_logVolume {X : Type*}
    (W : IQHullLogVolumeInterface X) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (h : W.logVolume W.hull ≤ ENNReal.ofReal θ) :
    iqHullRealVolume W ≤ θ :=
  (iqHullRealVolume_le_theta_iff W hθ0).mpr h

/-- **Theta-pilot IQ containment package.** Given a theta-pilot object whose
generator lies in the IQ packet, both the possible-image containment and the
product-map image containment into the tensor IQ packet hold. -/
theorem thetaPilot_iq_package
    {l : PrimeGeFive} {G : LGPMonoid l} {D : SourceLogShellDatum} {j : Nat}
    {P : LGPMonoidAction G Rat (sourceLogShellOnePlaceFamily D j)}
    (T : ThetaPilotObject P ())
    (hgen : T.generator ∈ sourceThetaPilotIQPacket D j) :
    T.possibleImage ⊆ sourceThetaPilotIQPacket D j ∧
      sourceThetaPilotProductMap D j '' T.possibleImage ⊆
        (sourceThetaPilotTensorIQPacket D j : Set D.K) :=
  ⟨possibleImage_subset_sourceThetaPilotIQPacket T hgen,
   sourceThetaPilotProductMap_image_subset_tensorIQPacket T hgen⟩

/-- **Finite real hull-volume via the realized log-volume** (consumer of the
ofReal identification): the real hull volume re-encodes the ENNReal hull
log-volume exactly. -/
theorem hull_logVolume_eq_ofReal_realVolume {X : Type*}
    (W : IQHullLogVolumeInterface X) :
    W.logVolume W.hull = ENNReal.ofReal (iqHullRealVolume W) :=
  iqHullLogVolume_hull_eq_ofReal W

#check hull_volume_package
#check thetaPilot_iq_package

end LeanFormal.IUT.XiFPaper.Mzk1ConsumerChainPackageActual
end