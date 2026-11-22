/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.gogopex.Iut.Stage1.CorollarySchema

/-! # A517: q/Theta pilot delta object from the signed comparison data -/

noncomputable section

namespace LeanFormal.IUT.Objects.GogopexPilotDelta

open Iut RealLineCopy

/-- The q/Theta pilot delta object: signed comparison data with concrete q/Theta magnitudes. -/
structure PilotDeltaObject where
  /-- The signed comparison data. -/
  data : Stage1.Corollary312ComparisonData
  /-- The signed Theta value. -/
  thetaSigned : Real
  /-- The signed q value. -/
  qSigned : Real
  theta_eq : thetaSigned = data.thetaSigned
  q_eq : qSigned = data.qSigned

/-- The object yields the Gogopex Corollary 3.12 signed inequality. -/
theorem PilotDeltaObject.corollary312 (D : PilotDeltaObject) :
    Stage1.Corollary312Inequality D.data.thetaPilot D.data.qPilot :=
  D.data.corollary312

/-- The signed q value is below the signed Theta value (three-term chain of two). -/
theorem PilotDeltaObject.q_le_theta (D : PilotDeltaObject) :
    D.qSigned ≤ D.thetaSigned := by
  rw [D.q_eq, D.theta_eq]
  exact D.data.qSigned_le_thetaSigned

/-- The q-pilot stored magnitude is positive. -/
theorem PilotDeltaObject.q_positive (D : PilotDeltaObject) :
    0 < D.data.qPilot.value :=
  D.data.qPilot_positive

end LeanFormal.IUT.Objects.GogopexPilotDelta
