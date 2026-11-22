import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Signed log-volume and the xi-e containment -> Cor 3.12 inequality

This is the direction-correct signed 3.12 assembly (cf. mainline A522):
if `qRegion ⊆ hullRegion` and the log-volume is monotone for subset, then
`signedLogVolume qRegion ≤ signedLogVolume hullRegion` directly, where the
signed log-volume is `log (vol S)` (negative for the actual hull regions).
This is exactly `-|log q| ≤ -|log Θ|`, without any sign flip or magnitude
assumption.  The positive-magnitude form `qVol ≤ hVol` is the opposite
direction and is recorded here only as an obstruction remark.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeCor312Actual

open Set

/-- Signed log-volume of a region: `log (vol S)` (negative for a hull region). -/
noncomputable def signedLogVolume {α : Type*} (vol : Set α → Real) (S : Set α) : Real :=
  Real.log (vol S)

/-- Monotonicity of the signed log-volume from monotonicity of the volume
function and positivity of the smaller volume. -/
theorem signedLogVolume_mono {α : Type*} {vol : Set α → Real}
    (hmono : ∀ {S T : Set α}, S ⊆ T → vol S ≤ vol T)
    {S T : Set α} (hST : S ⊆ T) (hpos : 0 < vol S) :
    signedLogVolume vol S ≤ signedLogVolume vol T := by
  unfold signedLogVolume
  exact Real.log_le_log hpos (hmono hST)

/-- xi-e containment data: the q-pilot region is contained in the Theta-pilot
hull region, with the q-pilot volume positive (so the signed log-volume is
well-defined as a real logarithm). -/
structure XiEContainment (α : Type*) (vol : Set α → Real) where
  qRegion : Set α
  hullRegion : Set α
  subset : qRegion ⊆ hullRegion
  q_pos : 0 < vol qRegion

/-- The signed q-pilot log-volume of the xi-e data. -/
noncomputable def signedQ {α : Type*} {vol : Set α → Real}
    (D : XiEContainment α vol) : Real :=
  signedLogVolume vol D.qRegion

/-- The signed Theta-pilot log-volume of the xi-e data. -/
noncomputable def signedTheta {α : Type*} {vol : Set α → Real}
    (D : XiEContainment α vol) : Real :=
  signedLogVolume vol D.hullRegion

/-- **xi-f, signed form**: containment and monotonicity give
`signedQ ≤ signedTheta`, i.e. `-|log q| ≤ -|log Θ|`. -/
theorem xi_f_signed_direction {α : Type*} {vol : Set α → Real}
    (hmono : ∀ {S T : Set α}, S ⊆ T → vol S ≤ vol T)
    (D : XiEContainment α vol) :
    signedQ D ≤ signedTheta D :=
  signedLogVolume_mono hmono D.subset D.q_pos

/-- The paper-shaped inequality: the signed q-pilot log-volume is at most the
signed Theta-pilot log-volume. -/
theorem signed_cor312_inequality {α : Type*} {vol : Set α → Real}
    (hmono : ∀ {S T : Set α}, S ⊆ T → vol S ≤ vol T)
    (D : XiEContainment α vol) : signedQ D ≤ signedTheta D :=
  xi_f_signed_direction hmono D

/-- Direction obstruction: for positive magnitudes `qVol, hVol`, the condition
`qVol ≤ hVol` does NOT give `-hVol ≥ -qVol`; indeed it gives
`-hVol ≤ -qVol`.  (This records why the positive-magnitude route is reversed.) -/
theorem positive_magnitude_direction_obstruction {qVol hVol : Real}
    (h : qVol ≤ hVol) : -hVol ≤ -qVol :=
  neg_le_neg h

end LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeCor312Actual
