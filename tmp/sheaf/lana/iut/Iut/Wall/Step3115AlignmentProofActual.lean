/--
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project, mainline lane (A494)
-/
import tmp.sheaf.lana.iut.Iut.WallEquiv.Gap
import tmp.sheaf.lana.iut.Iut.Wall.Checks
import tmp.sheaf.xif.paper.Mzk1QPilotR4Stage5AlignActual
import tmp.sheaf.xif.paper.Mzk1Step3115ComparisonActual
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual
import tmp.sheaf.xif.paper.Mzk1Step3115AlignmentProofActual

/-!
# Step-3115 readout alignment: definition analysis (A494)

Attempt to prove the two alignment equalities of `VariantOfStep3115Actual`:
(1) `qThetaHullReadout T b = (concreteVariantData D).qPilot.lhs`,
(2) `qThetaDetReadout T b = (concreteVariantData D).rhsData.rhs`.

Outcome of the definitional analysis (recorded, not papered over):

* Neither equality is definitional: the mainline readouts live on the native carriers
  (`qPilotLogImage T b = localSignedLog (qVFamily T b)`, a local signed completion log),
  while LANA's `(concreteVariantData D).qPilot.absLogQ` lives on `InitialThetaData`; the two
  are different models of the same paper quantity, so no `rfl` closes them.
* The **Theta side carries an explicit normalisation mismatch**: the mainline Theta readout
  is `qPilotLogImage / (2*l.value)` (the local root relation `theta^(2l) = q`), while the
  LANA `rhs = logVol(hull(Theta-pilot region))` is the procession-normalised volume whose
  Theta values are `q^{j²}` over the capsules (average `sFactor (nC D)`, see
  `Wall/logVol_lgp_integral` and `WallEquiv/Gap.gap_eq_rhs_add`).  Hence (2) is
  *equivalent to a normalisation statement* `rhs = lhs / (2*l.value)` once (1) is assumed;
  this is a DEFINITION/NORMALISATION difference between the local root reading and the
  global averaged procession volume, not a defect of the four-triangle comparison.

The file proves the conditional identities and the exact factor, so the remaining input of
`VariantOfStep3115Actual` is reduced to (1) plus the normalisation condition (2'), with no
sorry/axiom/True.
-/

namespace Iut

namespace Wall

universe u

open LeanFormal.IUT.XiFPaper.Mzk1QPilotR4Stage5AlignActual
open LeanFormal.IUT.XiFPaper.Mzk1Step3115ComparisonActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual

variable (D : InitialThetaData.{0})

/-- Definitional unfolding of the mainline hull readout. -/
theorem qThetaHullReadout_unfold {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) :
    qThetaHullReadout T b = localSignedLog (qVFamily T b) :=
  rfl

/-- Definitional unfolding of the mainline det readout: the local `2l`-root normalisation. -/
theorem qThetaDetReadout_unfold {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T)) :
    qThetaDetReadout T b = qPilotLogImage T b / (2 * (l.value : ℝ)) :=
  rfl

/-- LANA definitional form of the q-pilot side. -/
theorem concreteVariant_qPilot_lhs_unfold :
    (concreteVariantData D).qPilot.lhs = -D.qPilot.absLogQ :=
  rfl

/-- LANA definitional form of the right-hand side (hull of the Theta-pilot region). -/
theorem concreteVariant_rhs_unfold
    (labs : ∀ i : Fin (nC D), InitialThetaData.Lab (nC D) i) :
    (concreteVariantData D).rhsData.rhs = logVol D (hullOf D (thetaImage D labs)) :=
  rhs_eq_logVol_image D labs

/-- **Conditional normalisation identity:** assuming the q-pilot alignment (1), the det
  readout is `qPilot.lhs / (2l)` (unfold + root relation). -/
theorem det_eq_lhs_div_twoL_of_hull_alignment {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T))
    (h1 : qThetaHullReadout T b = (concreteVariantData D).qPilot.lhs) :
    qThetaDetReadout T b = (concreteVariantData D).qPilot.lhs / (2 * (l.value : ℝ)) := by
  rw [qThetaDetReadout_unfold, ← h1, qThetaHullReadout_unfold]

/-- **The exact normalisation condition for the det alignment (2):** given (1), (2) is
  equivalent to `rhs = lhs / (2 * l.value)`. -/
theorem det_alignment_iff_of_hull_alignment {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T))
    (h1 : qThetaHullReadout T b = (concreteVariantData D).qPilot.lhs) :
    (qThetaDetReadout T b = (concreteVariantData D).rhsData.rhs) ↔
      ((concreteVariantData D).rhsData.rhs =
        (concreteVariantData D).qPilot.lhs / (2 * (l.value : ℝ))) := by
  rw [det_eq_lhs_div_twoL_of_hull_alignment D T b h1]
  constructor
  · intro h; exact h.symm
  · intro h; exact h.symm

/-- **Audit corollary:** if both alignments hold, the LANA `rhs` must equal the local
  `lhs/(2l)` normalisation; combined with the LANA decomposition of `rhs`
  (`gap_eq_rhs_add_sFactor`) this pins the mismatch to the `sFactor` versus `1/(2l)`
  normalisations (model-level, not a proof gap of the comparison). -/
theorem alignment_forces_normalisation {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T))
    (h1 : qThetaHullReadout T b = (concreteVariantData D).qPilot.lhs)
    (h2 : qThetaDetReadout T b = (concreteVariantData D).rhsData.rhs) :
    (concreteVariantData D).rhsData.rhs =
      (concreteVariantData D).qPilot.lhs / (2 * (l.value : ℝ)) :=
  (det_alignment_iff_of_hull_alignment D T b h1).mp h2

end Wall

end Iut