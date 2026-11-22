import tmp.sheaf.xif.paper.Mzk1LatticeOrbitIndexActual
import tmp.sheaf.xif.paper.Mzk1PadicSaturationBasesActual
/-! #A1.6 signed relative readout on the measure side.

For compact open lattices `J <= O` in an additive Haar space, the signed
normalized log-mass difference is exactly minus the log of the lattice index.
This is the A2-based part of A1.6.  The remaining identity
`(1/d_F) log(mu(J)/mu(O)) = log||lambda||_L - delta` needs the normalized
valuation/ramification interface and the actual K/F lattices; it is not assumed.
-/
noncomputable section
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1A1SignedReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1LatticeOrbitIndexActual
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [MeasurableSpace E] [BorelSpace E]
/-- Signed normalized log-mass readout of `J` relative to `O`. -/
def signedRelativeReadout (μ : Measure E) (d : Nat) (J O : AddSubgroup E) : Real :=
  normalizedLogVolume μ d J - normalizedLogVolume μ d O
/-- Measure-side A1.6: if `J <= O` are compact open, then
`(1/d)(log mu(J) - log mu(O)) = -(1/d) log [O:J]`. -/
theorem signedRelativeReadout_eq_neg_log_index
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (d : Nat) {J O : AddSubgroup E} (hJO : J ≤ O)
    (hJc : IsCompact (J : Set E)) (hJo : IsOpen (J : Set E))
    (hOc : IsCompact (O : Set E)) (hOo : IsOpen (O : Set E))
    (hJpos : 0 < μ (J : Set E)) (hJtop : μ (J : Set E) < ⊤) :
    signedRelativeReadout μ d J O =
      - (1 / (d : Real)) * Real.log (latticeIndex J O : Real) := by
  have h := normalizedLogVolume_step μ d hJO hJc hJo hOc hOo hJpos hJtop
  unfold signedRelativeReadout
  linarith
/-- Exact remaining interface for the valuation half of A1.6; no comparison
or delta-small hypothesis is added in this file. -/
def a1SignedReadoutMissing : List String :=
  [ "normalized valuations v_F, v_L and ramification v_L(algebraMap x)=e*v_F(x)",
    "identification of the actual lambda-lattice index with p^(m - e*ceil(m/e))",
    "signed bound 0 <= delta < log p / e_F for the ceil remainder",
    "actual K/F lattices as PadicInt p-submodules with Z_p-bases" ]
theorem a1SignedReadoutMissing_length : a1SignedReadoutMissing.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1A1SignedReadoutActual
end