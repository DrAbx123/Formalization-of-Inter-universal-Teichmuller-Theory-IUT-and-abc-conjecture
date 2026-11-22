/- H-T 8.2 (third batch): assembly of route F2 from the per-place data, on sophie's 8.1
interface with the line-bundle heights.  The place sums are the conductor/different quantities;
the analytic input hdelta comes from LocalDifferentUpperBound / Mzk1LpDifferentBoundActual,
and hdifferent is the relative-different/tower consequence (batch2 log tower identities). -/
import tmp.sheaf.xif.paper.Mzk1G1ConductorDifferentCancellationCoreActual
import tmp.sheaf.xif.paper.Mzk1HT81InterfaceActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationAssemblyActual

open LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1HT81InterfaceActual

universe u

/-- Assembly data for route F2 over sophie's 8.1 interface: the per-place conductor/different
data together with the analytic inputs.

- hdelta : delta_{w/v} >= e_{w/v} - 1 (provenance: LocalDifferentUpperBound /
  Mzk1LpDifferentBoundActual);
- hdifferent : the relative-different term is bounded by D(L) - D(K_i) (provenance: the
  discriminant tower formula and the relative-different norm identity, batch2
  log_natAbs_discr_tower / log_absNorm_differentIdeal_eq).

NO INHABITANT until the corresponding 8.2 proofs provide the actual quantities. -/
structure F2PlaceWitness (H : HT81Interface) (i : H.I) (Hh : HT81LineBundleHeights H) where
  /-- the per-place conductor/different data -/
  places : LocalConductorDifferentData
  /-- the fixed constant C_i -/
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  /-- delta_{w/v} >= e_{w/v} - 1 at every place -/
  hdelta : ∀ w, places.e w - 1 ≤ places.differentExponent w
  /-- relative-different term <= D(L) - D(K_i) -/
  hdifferent : differentTerm places ≤ normalizedLogDisc H.L - normalizedLogDisc (H.K i)

/-- **Route F2 assembled from the place witness**: with the conductor-difference term as
N_D(phi_i(y)) - N_{E_i}(y) (the L-end normalization is absorbed into the constant), the
conductor/different cancellation inequality F2 holds. -/
theorem f2_of_witness (H : HT81Interface) (i : H.I) (Hh : HT81LineBundleHeights H)
    (W : F2PlaceWitness H i Hh) :
    F2 H i (ConductorDifferentData.mk (conductorDifference W.places) 0 (Hh.hEi i)
      W.constant) := by
  unfold F2
  have h1 : conductorDifference W.places ≤ differentTerm W.places :=
    conductorDifference_le_differentTerm W.places W.hdelta
  have h2 : conductorDifference W.places ≤
      normalizedLogDisc H.L - normalizedLogDisc (H.K i) := le_trans h1 W.hdifferent
  linarith [h2, W.constant_nonneg]

#print axioms f2_of_witness
end LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationAssemblyActual

