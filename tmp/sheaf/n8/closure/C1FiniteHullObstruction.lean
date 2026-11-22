import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring

/-!
  A finite-hull obstruction for the value-monoid realization.

  Under pointwise degree faithfulness, the source holomorphic hull is forced to
  have top volume.  Therefore any downstream bridge requiring a finite hull is
  incompatible with that realization; this is independent of the q-pilot
  output-membership question.
-/

noncomputable section

namespace LeanFormal.IUT.Theorem311Source.OriginalInput

open LeanFormal.IUT

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem no_finite_sourceHullVolume_of_degreeFaithful
    (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ I.sourceHullVolume v R n < ⊤ := by
  intro hfin
  have htop : I.sourceHullVolume v R n = ⊤ :=
    I.sourceHullVolume_eq_top_of_degreeFaithful v R n hdeg
  rw [htop] at hfin
  exact (lt_irrefl (⊤ : ENNReal)) hfin

end LeanFormal.IUT.Theorem311Source.OriginalInput

end

#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.no_finite_sourceHullVolume_of_degreeFaithful
