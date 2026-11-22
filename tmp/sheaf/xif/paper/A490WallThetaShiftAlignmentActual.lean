/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.lana.iut.Iut.Wall.MultiContainer

/-! # A490 NumericalWall squad: wall + theta-shift numeric alignment -/

namespace Iut

namespace Wall

variable (D : InitialThetaData.{0})

/-- Under the wall hypothesis and the identified-copies theta-shift law, every pair of Hodge
theaters admits an (Ind3)-choice whose log-volume satisfies the wall equation
`-s|log q| + logVol(S) = qPilot.lhs`. -/
theorem wall_thetaShift_logVol (A : EtaAlg D) (hW : Wall D A) (hS : A.ThetaShift) :
    ∀ h₁ h₂ : A.Side, ∃ S : Ind3 D,
      -(sFactor (nC D) * D.qPilot.absLogQ) + logVol D S.1 =
        (concreteVariantData D).qPilot.lhs := by
  intro h₁ h₂
  obtain ⟨ι, S, hη⟩ := (A.wall_iff_forall).mp hW h₁ h₂
  refine ⟨S, ?_⟩
  have hvol : logVol D (A.out ι S) = (concreteVariantData D).qPilot.lhs := 
    (A.etaAnab_eq_etaQ_iff ι S).mp hη
  rw [← hvol, hS ι S]

/-- Consequently the region selected by the wall has log-volume `qPilot.lhs` and the
theta-shift law re-expresses it as `-s|log q| + logVol(S)`. -/
theorem wall_region_logVol_eq_qPilot (A : EtaAlg D) (hW : Wall D A) :
    ∃ U : Region D, IsAdelic D U ∧ InHullOfImage D U ∧
      logVol D U = (concreteVariantData D).qPilot.lhs :=
  A.exists_out_of_wall hW

end Wall

end Iut
