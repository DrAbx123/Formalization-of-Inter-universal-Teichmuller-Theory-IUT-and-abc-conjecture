/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A744: direct SSIneq attack — reduction to the LGP·hull log-volume bound -/

/- Strategy (A744): absorb lana, use `idAlgOn` so that the wall is `SSIneq D`
(`Wall/Constraints.lean:304 wall_idAlgOn_iff`), and reduce `SSIneq D` via lana's
identified-copies law.

lana definitions/lemmas that the attack must consume (all read from repo root Iut/):
* `SSIneq D := (sFactor (nC D) - 1) * D.qPilot.absLogQ <= logVol D (hullOf D (vcI D))`
  (Iut/Wall/MultiContainer.lean:88); here neither the inequality nor its negation is proved
  (module docstring, l.86-87);
* `idAlgOn D sigma` (Iut/Wall/Constraints.lean:272): identified-copies eta-algorithm with
  `out _ S := lgp D S.1`, realisation `⟨isAdelic_lgp D S.2.1, inHullOfImage_lgp D S⟩`;
* `wall_idAlgOn_iff` (Constraints.lean:304): `Wall D (idAlgOn D sigma) <-> SSIneq D`;
* identified-copies law: `logVol_lgp` + `logVol_lgp_integral` give
  `logVol D (lgp D U) = logVol D U - s*|log q|` (HodgeTheater/Wall.lean:158 rewrites with
  `logVol_lgp D S.2.1, logVol_lgp_integral`);
* `logVol_lgp_vcI_le_rhs` / `gap_nonneg` (Iut/WallEquiv/Gap.lean:510-514):
  `logVol D (lgp D (hullOf D (vcI D))) <= rhs` where `rhs = -|log Theta|`;
* `inHullOfImage_lgp`, `isAdelic_lgp` (realisation facts).

Status in our build: the `Iut/Wall/*` and `Iut/WallEquiv/*` oleans are NOT built here
(only Iut/Abc, Iut/Anabelian, Iut/Concrete dirs have oleans), so the attack cannot yet import
them directly; the reduction below is the content that would consume them, formalized over
real numbers, with the hypothesis being exactly lana's identified-copies identity.

Remaining genuine target (A744 step 3): find `S : Ind3 D` (or U) with
  `-|log q| <= logVol D (lgp D U)` and `U` in the hull; via the identity below this is
equivalent to `SSIneq D` itself, so it is the open Scholze–Stix content, not a lemma of the
model.  No fake proof is produced. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1SSIneqDirectAttackActual

/-- `SSIneq` in scalar form: `(s-1)*|log q| <= hullLogVol`. -/
def SSIneqScalar (s absLogQ hullLogVol : ℝ) : Prop :=
  (s - 1) * absLogQ ≤ hullLogVol

/-- The identified-copies identity `logVol (lgp D U) = logVol U - s*|log q|`. -/
def LgpIdentifiedCopies (s absLogQ volU volLgpU : ℝ) : Prop :=
  volLgpU = volU - s * absLogQ

/-- **Reduction**: under the identified-copies identity, the target inequality
`-|log q| <= logVol (lgp D (hullOf D (vcI D)))` is EQUIVALENT to `SSIneq D`. -/
theorem ssIneq_iff_lgp_bound (s absLogQ hullLogVol lgpVol : ℝ)
    (h : LgpIdentifiedCopies s absLogQ hullLogVol lgpVol) :
    SSIneqScalar s absLogQ hullLogVol ↔ -absLogQ ≤ lgpVol := by
  unfold SSIneqScalar LgpIdentifiedCopies at *
  constructor <;> intro hh <;> nlinarith

/-- Hence a proof of the LGP·hull log-volume bound yields `SSIneq` (via lana's
`wall_idAlgOn_iff` this yields the wall for `idAlgOn`). -/
theorem ssIneq_of_lgp_bound (s absLogQ hullLogVol lgpVol : ℝ)
    (h : LgpIdentifiedCopies s absLogQ hullLogVol lgpVol)
    (hlgp : -absLogQ ≤ lgpVol) : SSIneqScalar s absLogQ hullLogVol :=
  (ssIneq_iff_lgp_bound s absLogQ hullLogVol lgpVol h).mpr hlgp

/-- Exact remaining target (not proved): the LGP·hull bound. -/
def LgpBoundTarget (absLogQ lgpVol : ℝ) : Prop := -absLogQ ≤ lgpVol

end LeanFormal.IUT.XiFPaper.Mzk1SSIneqDirectAttackActual
