import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmKernel
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The actual quotient topology agrees with the logarithmic-image topology

The torsion quotient retains the quotient topology of the compact full
integral unit group. Its canonical logarithmic image has the subspace
topology of the field. The proved bijection is a homeomorphism by
compactness and Hausdorffness, with its value on actual units unchanged.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

include localNormedAlgebra

theorem continuous_unitLogTorsionQuotientEquivRange :
    Continuous (unitLogTorsionQuotientEquivRange (K := K) (p := p)) := by
  apply (QuotientGroup.isQuotientMap_mk (CommGroup.torsion (Integers K)ˣ)).continuous_iff.mpr
  change Continuous (fun u : (Integers K)ˣ =>
    (⟨unitLogHom (p := p) u, ⟨u, rfl⟩⟩ : (unitLogHom (K := K) (p := p)).range))
  exact (continuous_unitLog (p := p)).subtype_mk _

/-- This homeomorphism uses the original quotient topology, rather than
declaring the topology by transport from a desired target. -/
def unitLogTorsionQuotientHomeomorph :
    ((Integers K)ˣ ⧸ CommGroup.torsion (Integers K)ˣ) ≃ₜ
      (unitLogHom (K := K) (p := p)).range := by
  letI := compactSpace_units (K := K)
  let e := (unitLogTorsionQuotientEquivRange (K := K) (p := p)).toEquiv
  have hc : Continuous e := continuous_unitLogTorsionQuotientEquivRange (p := p)
  exact e.toHomeomorphOfContinuousClosed hc hc.isClosedMap

theorem unitLogTorsionQuotientHomeomorph_mk (u : (Integers K)ˣ) :
    (unitLogTorsionQuotientHomeomorph (p := p) (QuotientGroup.mk u)).val =
      Multiplicative.ofAdd (unitLog u) := rfl

end

end LeanFormal.IUT.LocalFieldLogarithm
