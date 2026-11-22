import LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardAMPLThetaBoundSupply
import LeanFormal/IUT/IUTIII/Corollary312/StepXI/CertificateHullWiring

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1HullAmplCertificateEquivActual — A479 real equivalence consumers

New **equivalence** theorems combining the AMPL theta-bound supply
(`CardAMPLThetaBoundSupply.lean:116/125`), the real-volume interface-correction
equivalence (`CertificateHullWiring.lean:106`) and the ofReal hull-volume
identification (:99):

1. `ampl_supply_iff_real_bound`: a supply exists iff some nonnegative real
   constant bounds the real hull volume;
2. `certificate_bound_iff_real_bound`: an ENNReal bound on the hull log-volume
   exists iff a nonnegative real bound on the real hull volume exists.

No sorry/axioms; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullAmplCertificateEquivActual

open LeanFormal.IUT

/-- **Supply existence iff real bound.** -/
theorem ampl_supply_iff_real_bound {X : Type*} (W : IQHullLogVolumeInterface X) :
    Nonempty (CardAMPLThetaBoundSupply W) ↔
      ∃ θ : Real, 0 ≤ θ ∧ iqHullRealVolume W ≤ θ := by
  rw [CardAMPLThetaBoundSupply.nonempty_iff]
  constructor
  · rintro ⟨θ, hθ0, hθ⟩
    exact ⟨θ, hθ0, (iqHullRealVolume_le_theta_iff W hθ0).mpr hθ⟩
  · rintro ⟨θ, hθ0, hθ⟩
    exact ⟨θ, hθ0, (iqHullRealVolume_le_theta_iff W hθ0).mp hθ⟩

/-- **Certificate bound iff real bound.** -/
theorem certificate_bound_iff_real_bound {X : Type*} (W : IQHullLogVolumeInterface X) :
    (∃ θ : Real, 0 ≤ θ ∧ W.logVolume W.hull ≤ ENNReal.ofReal θ) ↔
      ∃ θ : Real, 0 ≤ θ ∧ iqHullRealVolume W ≤ θ := by
  constructor
  · rintro ⟨θ, hθ0, hθ⟩
    exact ⟨θ, hθ0, (iqHullRealVolume_le_theta_iff W hθ0).mpr hθ⟩
  · rintro ⟨θ, hθ0, hθ⟩
    exact ⟨θ, hθ0, (iqHullRealVolume_le_theta_iff W hθ0).mp hθ⟩

#check ampl_supply_iff_real_bound
#check certificate_bound_iff_real_bound

end LeanFormal.IUT.XiFPaper.Mzk1HullAmplCertificateEquivActual
end