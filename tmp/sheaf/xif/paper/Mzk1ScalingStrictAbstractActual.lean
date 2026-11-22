import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Mzk1ScalingStrictAbstractActual — abstract scaling strict chain (R/p)

A561 chain-independent module (no new mathematics): the abstract form of the
R/p-scaling strict chain — positive volumes on the q-region and hull with strict
increase; the signed log-volumes are strictly ordered and yield a StepXI contract and
Cor 3.12 conclusion.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ScalingStrictAbstractActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual

universe u

/-- R/p scaling strict data: a monotone volume functional with a strictly positive
volume of the q-region and a strict increase on the hull. -/
structure RPStrictData (α : Type u) where
  vol : Set α → Real
  vol_mono : ∀ {S T : Set α}, S ⊆ T → vol S ≤ vol T
  qRegion : Set α
  hullRegion : Set α
  subset : qRegion ⊆ hullRegion
  q_pos : 0 < vol qRegion
  strict_measure : vol qRegion < vol hullRegion

namespace RPStrictData

variable {α : Type u} (D : RPStrictData α)

/-- The signed q-pilot value: log of the q-region volume. -/
noncomputable def rpSignedQ (D : RPStrictData α) : Real := Real.log (D.vol D.qRegion)

/-- The signed Theta-pilot value: log of the hull volume. -/
noncomputable def rpSignedTheta (D : RPStrictData α) : Real := Real.log (D.vol D.hullRegion)

/-- Strictness of the signed comparison from the strict volume increase. -/
theorem rpSigned_strict (D : RPStrictData α) :
    D.rpSignedQ < D.rpSignedTheta :=
  Real.log_lt_log D.q_pos D.strict_measure

/-- The non-strict signed comparison. -/
theorem rpSigned_le (D : RPStrictData α) : D.rpSignedQ ≤ D.rpSignedTheta :=
  le_of_lt D.rpSigned_strict

/-- The R/p contract: signed slots from the volumes, comparison from the strict
increase, with the q-pilot sign `rpSignedQ < 0` as an explicit paper hypothesis. -/
noncomputable def rpContract (D : RPStrictData α) (hqneg : D.rpSignedQ < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) : StepXIContract :=
  signedCor312Contract D.rpSignedQ D.rpSignedTheta hqneg
    ipl hipl she hshe apt hapt D.rpSigned_le

/-- Cor 3.12 conclusion of the R/p contract. -/
theorem rpCor312 (D : RPStrictData α) (hqneg : D.rpSignedQ < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (D.rpContract hqneg ipl hipl she hshe apt hapt) :=
  signedCor312_conclusion D.rpSignedQ D.rpSignedTheta hqneg
    ipl hipl she hshe apt hapt D.rpSigned_le

end RPStrictData

#check RPStrictData
#check RPStrictData.rpSignedQ
#check RPStrictData.rpSignedTheta
#check RPStrictData.rpSigned_strict
#check RPStrictData.rpContract
#check RPStrictData.rpCor312

end LeanFormal.IUT.XiFPaper.Mzk1ScalingStrictAbstractActual
end
