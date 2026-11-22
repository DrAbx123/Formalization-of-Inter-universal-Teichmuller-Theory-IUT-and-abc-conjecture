/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A745: SSIneq hull lower bound — target reduction + lana lemma inventory -/

/- lana inventory (repo-root Iut/, read-only; oleans for Iut/Wall/* are NOT built here):
* `nC D := (D.ℓ - 1)/2` (Wall/Rss.lean:303), `nC_pos` (:305);
* `VC := LocalTheory.container D.placeSect (nC D)` (:311);
* `Region D := ∀ i : Fin (VC D).proc.length, (VC D).AdmissibleRegion i` (:314);
* `IsAdelic U` (:319) — every packet region admissible (nonempty, rel. compact,
  measurable, positive finite Haar measure; all but finitely many integral);
* `logVol U := (LocalTheory.vol D.placeSect (nC D)).processionVol U` (:324);
* `hullOf U := (LocalTheory.hull D.placeSect (nC D)).hullFamily U` (:328);
* `thetaImage l := D.thetaPilotOn (nC D) (fun i => {l i}) ...` (:333);
* `InHullOfImage U := ∃ l, ∀ i, U i ≤ hullOf D (thetaImage D l) i` (:338);
* `sFactor n = (∑ j ∈ range n, (j+1)^2)/n` (Wall/Pilots.lean:55);
* `SSIneq D := (sFactor (nC D) - 1) * D.qPilot.absLogQ <= logVol D (hullOf D (vcI D))`
  (Wall/MultiContainer.lean:88; module docstring: neither it nor its negation is proved);
* `Wall D A ↔ SSIneq D` (Wall/Constraints.lean:204,305,312,316 for idAlg/idAlgOn);
* `IdAlgOn` realisation: `out _ S := lgp D S.1`, `realisation _ S := ⟨isAdelic_lgp D S.2.1,
  inHullOfImage_lgp D S⟩` (Constraints.lean:272-280);
* `logVol_lgp` + `logVol_lgp_integral` (Wall/HodgeTheater.lean:158) give the identified-copies
  law; `logVol_lgp_vcI_le_rhs`, `gap_nonneg`, `gap_eq_rhs_add` (WallEquiv/Gap.lean:510-525);
* `WallEquiv/VcI.md:61`: `logVol_hull_vcI_eq : logVol D (hullOf D (vcI D)) =
  (∑_i ∑ᶠ hullPacket)/ℓ*`, with `hullPacket` the weighted packet hull volumes.

Remaining mathematical step: the hull lower bound
  `(s-1)*|log q| <= logVol D (hullOf D (vcI D))`
is exactly `SSIneq`; lana proves the container/hull volume FORMULA (VcI) but not the
inequality, and no lemma in Concrete/Wall currently closes it (the model docs state this is
the open Scholze–Stix content).  Below: the arithmetic reduction that a future hull-packet
lower bound would feed, plus the formula shape from VcI.md. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1SSINeqHullLowerActual

/-- The target inequality in scalar form. -/
def ssIneqHullLowerTarget (s absLogQ hullVol : ℝ) : Prop := (s - 1) * absLogQ ≤ hullVol

/-- **Reduction via the VcI hull-volume formula**: if the hull log-volume equals the
procession average `hullSum / ellStar` of the packet hull volumes (VcI.md:61), then the target
follows from a lower bound on the packet-hull sum. -/
theorem ssIneqHullLower_of_packetSum {s absLogQ hullVol hullSum ellStar : ℝ}
    (hell : 0 < ellStar) (hformula : hullVol = hullSum / ellStar)
    (hpacket : (s - 1) * absLogQ * ellStar ≤ hullSum) :
    ssIneqHullLowerTarget s absLogQ hullVol := by
  unfold ssIneqHullLowerTarget
  rw [hformula]
  rw [le_div_iff₀ hell]
  linarith

/-- Equivalent form: a lower bound `hullVol >= (s-1)*|log q|` is exactly the target. -/
theorem ssIneqHullLower_iff (s absLogQ hullVol : ℝ) :
    ssIneqHullLowerTarget s absLogQ hullVol ↔ (s - 1) * absLogQ ≤ hullVol := Iff.rfl

/-- The arithmetic core of `idAlgOn`'s identified-copies law: if
`logVol (lgp U) = logVol U - s*|log q|` (logVol_lgp/logVol_lgp_integral), then the target is
equivalent to `-|log q| <= logVol (lgp (hullOf vcI))`. -/
theorem target_iff_lgpBound {s absLogQ hullVol lgpVol : ℝ}
    (hid : lgpVol = hullVol - s * absLogQ) :
    ssIneqHullLowerTarget s absLogQ hullVol ↔ -absLogQ ≤ lgpVol := by
  unfold ssIneqHullLowerTarget
  constructor <;> intro h <;> nlinarith

end LeanFormal.IUT.XiFPaper.Mzk1SSINeqHullLowerActual
