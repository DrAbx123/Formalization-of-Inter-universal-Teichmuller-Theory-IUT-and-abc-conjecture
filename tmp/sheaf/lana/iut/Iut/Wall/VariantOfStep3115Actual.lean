/--
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project, mainline lane (A493)
-/
import tmp.sheaf.lana.iut.Iut.WallEquiv.Gap
import tmp.sheaf.lana.iut.Iut.Wall.Checks
import tmp.sheaf.xif.paper.Mzk1QPilotR4Stage5AlignActual
import tmp.sheaf.xif.paper.Mzk1Step3115ComparisonActual

/-!
# The Corollary 3.12 variant from the step-3115 readouts (A493)

We do **not** pursue `gap D = 0` (audit note: `gap D >= 0`, and `gap = 0` (SSIneq) is
STRICTLY STRONGER than the variant (Var) needed for Corollary 3.12; LANA
`WallEquiv/Gap.lean` proves `SSIneq -> Corollary312Variant` but not the converse).
The target here is exactly (Var):

  `qPilot.lhs = -|log q| <= rhs = logVol(hull(Theta-pilot region))`.

Mainline data:
* `qThetaHullReadout T b` (signed q-pilot log-volume),
* `qThetaDetReadout T b` (signed Theta-pilot log-volume),
* `qThetaReadout_ordered` / `step3115_comparison_proved`: `hullReadout <= detReadout`.

The two definition-level identifications with `concreteVariantData D` are recorded as an
explicit alignment structure (they compare the native Theta-data readouts `T` with the
LANA `InitialThetaData` quantities `D`; they are not definitional across the two
representations, so they are explicit named inputs, not hidden axioms).

No sorry/axiom/True.
-/

namespace Iut

namespace Wall

universe u

open LeanFormal.IUT.XiFPaper.Mzk1QPilotR4Stage5AlignActual
open LeanFormal.IUT.XiFPaper.Mzk1Step3115ComparisonActual

variable (D : InitialThetaData.{0})

/-- The q-pilot lhs of the concrete variant data is `-|log q|` (definitional). -/
theorem qPilot_lhs_eq_neg_absLogQ :
    (concreteVariantData D).qPilot.lhs = -D.qPilot.absLogQ :=
  rfl

/-- **The rhs is the log-volume of the holomorphic hull of the Theta-pilot region**
  (the `concreteVariantData` construction, at any label placement). -/
theorem rhs_eq_hull_thetaImage_logVol
    (l : ∀ i : Fin (nC D), InitialThetaData.Lab (nC D) i) :
    (concreteVariantData D).rhsData.rhs = logVol D (hullOf D (thetaImage D l)) :=
  rhs_eq_logVol_image D l

/-- **The definition-level alignment of the mainline readouts with the LANA quantities**
  (two named inputs, one per readout):
  (1) the signed q-pilot readout is `qPilot.lhs = -|log q|`;
  (2) the signed Theta-pilot readout is `rhs = logVol(hull(Theta-pilot region))`. -/
structure Step3115ReadoutAlignment {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) : Prop where
  /-- (1) q-pilot readout ↔ `qPilot.lhs = -|log q|`. -/
  hull_eq : qThetaHullReadout T b = (concreteVariantData D).qPilot.lhs
  /-- (2) Theta-pilot readout ↔ `rhs = logVol(hull(Theta-pilot region))`. -/
  det_eq : qThetaDetReadout T b = (concreteVariantData D).rhsData.rhs

/-- **Corollary 3.12 (Var) from the step-3115 comparison + readout alignment:**
  `-|log q| <= rhs`. -/
theorem variant_of_step3115_readouts {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T))
    (A : Step3115ReadoutAlignment D T b) :
    Corollary312Variant (concreteVariantData D) := by
  rw [variant_iff_le_rhs]
  rw [← A.hull_eq, qPilot_lhs_eq_neg_absLogQ D, ← A.det_eq]
  exact qThetaReadout_ordered T b

/-- **Explicit form with the two equalities as hypotheses** (no structure). -/
theorem variant_of_step3115_readouts_exp {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T))
    (h_hull : qThetaHullReadout T b = (concreteVariantData D).qPilot.lhs)
    (h_det : qThetaDetReadout T b = (concreteVariantData D).rhsData.rhs) :
    Corollary312Variant (concreteVariantData D) := by
  rw [variant_iff_le_rhs]
  rw [← h_hull, qPilot_lhs_eq_neg_absLogQ D, ← h_det]
  exact qThetaReadout_ordered T b

/-- The variant through the built-in `StepXIContract` comparison (same content, contract
  slot form): the filled four-triangle instance yields the Cor 3.12 ordered conclusion. -/
theorem variant_of_qThetaFourTriangle {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T))
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    Cor312Conclusion (qThetaFourTriangleSynthesis T b ipl hipl apt hapt).contract :=
  cor312Conclusion_of_fourTriangleSynthesis _

end Wall

end Iut