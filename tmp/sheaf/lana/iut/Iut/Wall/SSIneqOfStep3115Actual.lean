/--
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project, mainline lane (A491)
-/
import tmp.sheaf.lana.iut.Iut.WallEquiv.Gap
import tmp.sheaf.lana.iut.Iut.Wall.MultiContainer
import tmp.sheaf.xif.paper.Mzk1QPilotR4Stage5AlignActual
import tmp.sheaf.xif.paper.Mzk1Step3115ComparisonActual

/-!
# SSIneq from the step-3115 q/Theta readouts (A491)

Mapping between the mainline q/Theta readouts (`Mzk1QPilotR4Stage5AlignActual`:
`qThetaHullReadout` for the signed q-pilot log-volume, `qThetaDetReadout` for the signed
Theta-pilot log-volume, `qThetaReadout_ordered` for the Step (xi-f) signed comparison) and
LANA's Scholze–Stix inequality `Wall.SSIneq`
(sFactor(nC) − 1)·|log q| ≤ logVol(hull(VC(I))), `Iut/Wall/MultiContainer.lean:88`).

Two mapping equalities are the explicit named inputs (they identify the readouts with the
LANA quantities):
* `qThetaHullReadout T b = -D.qPilot.absLogQ` (signed q-pilot log-volume);
* `qThetaDetReadout T b = (concreteVariantData D).rhsData.rhs` (signed Theta-pilot
  log-volume `-|log(Theta)|`).

From the Step (xi-f) comparison `hullReadout <= detReadout` we derive the Corollary 3.12
variant `Corollary312Variant (concreteVariantData D)`.  To obtain `SSIneq D` we need the
remaining gap to vanish (`Wall.gap D = 0`; `WallEquiv/Gap.lean:504` defines it as the
difference of the two right-hand sides); this is the explicit named gap, never assumed
globally.  No sorry/axiom/True.
-/

namespace Iut

namespace Wall

universe u

open LeanFormal.IUT.XiFPaper.Mzk1QPilotR4Stage5AlignActual
open LeanFormal.IUT.XiFPaper.Mzk1Step3115ComparisonActual

variable (D : InitialThetaData.{0})

/-- **The variant from the step-3115 readouts**: if the signed q-pilot readout is
  `-|log q|` and the signed Theta readout is `rhs = -|log(Theta)|`, the Step (xi-f)
  comparison gives the Corollary 3.12 variant. -/
theorem variant_of_step3115_readouts {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T))
    (h_hull : qThetaHullReadout T b = -D.qPilot.absLogQ)
    (h_det : qThetaDetReadout T b = (concreteVariantData D).rhsData.rhs) :
    Corollary312Variant (concreteVariantData D) := by
  rw [variant_iff_le_rhs]
  rw [← h_hull, ← h_det]
  exact qThetaReadout_ordered T b

/-- **The explicit named gap for the SSIneq mapping**: the gap `Delta(D)` between the
  variant right-hand side and the LANA hull log-volume vanishes.  This is the remaining
  IUT IV/T1 content; it is an explicit argument, not a hidden axiom. -/
structure SSIneqStep3115Gap where
  gap_zero : gap D = 0

/-- **`SSIneq` from the step-3115 readouts plus the vanishing gap**: the Scholze–Stix
  inequality follows from the variant (step-3115 comparison + readout mapping),
  `ssIneq_of_noHull`-free: `ss_iff_variant_of_gap_eq_zero`. -/
theorem ssIneq_of_step3115_readouts {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T))
    (h_hull : qThetaHullReadout T b = -D.qPilot.absLogQ)
    (h_det : qThetaDetReadout T b = (concreteVariantData D).rhsData.rhs)
    (G : SSIneqStep3115Gap D) : SSIneq D :=
  (ss_iff_variant_of_gap_eq_zero D G.gap_zero).mpr
    (variant_of_step3115_readouts D T b h_hull h_det)

/-- **The named gap in its hull-log-volume form** (equivalent to `gap D = 0`): the
  log-volume of `LGP . hull(VC(I))` equals the variant right-hand side, i.e. the step-3115
  Theta readout. -/
theorem gap_eq_zero_iff_logVol_lgp :
    gap D = 0 ↔ logVol D (lgp D (hullOf D (vcI D))) =
      (concreteVariantData D).rhsData.rhs := by
  unfold gap
  constructor
  · intro h
    linarith
  · intro h
    rw [h, sub_self]

/-- **The explicit named gap in its precise LGP-hull form**: the log-volume of
  `LGP . hull(VC(I))` equals the variant right-hand side `-|log(Theta)|`.  This is
  exactly `gap D = 0`; it is the remaining normalization statement (the theta-pilot hull
  volume versus the LGP-image hull volume), NOT derivable from the signed q/Theta
  comparison alone — `WallEquiv/Gap.lean` only gives the inequality
  `logVol_lgp_vcI_le_rhs`.  Declared as an explicit argument, never a hidden axiom. -/
def LgpHullRhsInput : Prop :=
  logVol D (lgp D (hullOf D (vcI D))) = (concreteVariantData D).rhsData.rhs

/-- The LGP-hull/rhs equality is exactly the vanishing of the gap. -/
theorem gap_eq_zero_iff_lgpHullRhsInput : gap D = 0 ↔ LgpHullRhsInput D :=
  gap_eq_zero_iff_logVol_lgp D

/-- The LGP-hull equality gives the Scholze–Stix inequality, using the LGP law
  `logVol_lgp` and the variant form; equivalently it is the "no gap" case of
  `ss_iff_variant_of_gap_eq_zero`. -/
theorem ssIneq_of_lgpHullRhsInput (h : LgpHullRhsInput D) :
    SSIneq D ↔ Corollary312Variant (concreteVariantData D) :=
  ss_iff_variant_of_gap_eq_zero D ((gap_eq_zero_iff_lgpHullRhsInput D).mpr h)

/-- **The step-3115 route to SSIneq with the explicit LGP-hull gap**: from the readout
  mapping, the Step (xi-f) comparison, and the named LGP-hull/rhs equality, the
  Scholze–Stix inequality follows. -/
theorem ssIneq_of_step3115_and_lgpHullRhs {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T))
    (h_hull : qThetaHullReadout T b = -D.qPilot.absLogQ)
    (h_det : qThetaDetReadout T b = (concreteVariantData D).rhsData.rhs)
    (hgap : LgpHullRhsInput D) : SSIneq D :=
  ((ssIneq_of_lgpHullRhsInput D hgap)).mpr
    (variant_of_step3115_readouts D T b h_hull h_det)

/-! ### LANA quantity decomposition used by the named gap

These re-exports record exactly which LANA quantities the named gap compares:
`sFactor (nC D)`, `|log q| = D.qPilot.absLogQ`, and `logVol(hull(VC(I)))`. -/

/-- The LGP law at the hull of the container: the log-volume of `LGP . hull(VC(I))`
  is the log-volume of `LGP . O` plus the hull log-volume. -/
theorem lgp_hull_logVol_decomp :
    logVol D (lgp D (hullOf D (vcI D))) =
      logVol D (lgp D (integralRegion D)) + logVol D (hullOf D (vcI D)) :=
  logVol_lgp D (isAdelic_hullOf_vcI D)

/-- The log-volume of `LGP . O` is `-s . |log q|` with `s = sFactor (nC D)`. -/
theorem lgp_integral_logVol_eq :
    logVol D (lgp D (integralRegion D)) =
      -(sFactor (nC D) * D.qPilot.absLogQ) :=
  logVol_lgp_integral D

/-- The gap is exactly the difference of the two right-hand sides. -/
theorem gap_eq_rhs_sub_lgp_hull :
    gap D = (concreteVariantData D).rhsData.rhs -
      logVol D (lgp D (hullOf D (vcI D))) :=
  rfl

/-- In LANA quantities: `gap = rhs + s . |log q| - logVol(hull(VC(I)))`
  (the decomposition of `gap_eq_rhs_add`). -/
theorem gap_eq_rhs_add_sFactor :
    gap D = (concreteVariantData D).rhsData.rhs +
      sFactor (nC D) * D.qPilot.absLogQ - logVol D (hullOf D (vcI D)) :=
  gap_eq_rhs_add D

/-- The named LGP-hull gap, equivalently as a hull-log-volume normalization:
  `logVol(hull(VC(I))) = rhs + s . |log q|`. -/
theorem lgpHullRhsInput_iff_hull_logVol_eq :
    LgpHullRhsInput D ↔
      logVol D (hullOf D (vcI D)) =
        (concreteVariantData D).rhsData.rhs + sFactor (nC D) * D.qPilot.absLogQ := by
  rw [← gap_eq_zero_iff_lgpHullRhsInput, gap_eq_rhs_add_sFactor]
  constructor <;> intro h <;> linarith

end Wall

end Iut