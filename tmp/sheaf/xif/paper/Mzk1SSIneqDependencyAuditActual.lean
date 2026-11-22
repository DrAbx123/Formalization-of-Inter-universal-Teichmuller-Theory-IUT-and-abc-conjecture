/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-! # A738: SSIneq dependency/status audit (lana ThetaLink/Wall + LogLink/Thm311, read-only) -/

/- Sources (all read-only):
* Iut/Wall/MultiContainer.lean:88 `def SSIneq (D : InitialThetaData.{0}) : Prop`;
  (per Thm311.lean:49) `SSIneq D : (s - 1) * |log q| <= log-vol(hull(VC(I)))`.
* Iut/ThetaLink/Wall.lean:32-52 results & scope: for every `LinkedChain D`
  (`kummerVolCompat`, `volCompat`, `distortion_eq_zero`), `wallOn_thetaRow_iff` and
  `wall3_iff` identify the wall along Theta-links with `SSIneq D`; the M3 drift example
  `Wall.chainModel D k` is not log-shell compatible for k != 0 (kummer identifications move
  value-group data into the unit portion).  Scope note (l.54-60): whether an actual
  eta-algorithm through the Theta-link has this output law is NOT decided here (that is the
  content of IUT III Thm 3.11 / Cor 3.12, roadmap P20-P22); log-shell compatibility is a
  hypothesis field of `LinkedChain`, argued but not derived.
* Iut/LogLink/Thm311.lean:38-67: `XiPrinciple K` = the wall of the multi-container model
  along horizontal arrows, an EXPLICIT hypothesis; `variant_of_thm311`, `wall_of_thm311`,
  `classicalABC_of_thm311` are conditional on `Thm311 L K` + `XiPrinciple K`;
  `xi_iff_ss` says Step (xi) IS `SSIneq D`.  The model does not prove or refute `SSIneq D`
  (l.59-67); the log-theta-lattice in this model gives the identified-copies output law
  `log-vol(LGP*S) = -s*|log q| + log-vol(S)` (ThetaShift), also for alien Kummer data, and
  no different output law is produced by the structure.

## Dependency/status summary (audit; nothing beyond the constructed model is claimed)
* `SSIneq D` is a *Prop* over concrete initial Theta-data; in the model it is equivalent to
  the wall (`wallOn_thetaRow_iff`, `wall3_iff`) and to Step (xi) (`xi_iff_ss`).
* The ABC chain is conditional: Thm311 (explicit hypothesis) + XiPrinciple (= SSIneq) =>
  Cor312 variant (`variant_of_thm311`), wall input (`wall_of_thm311`), ClassicalABC
  (`classicalABC_of_thm311`, via `Wall.classicalABC_of_wall`).
* `SSIneq D` is NOT proved and NOT refuted in the model; it is the remaining substantive
  input, matching our `abcbridge:Cor312EpsilonArithmeticComparison` named gaps role.
* Modelling conditions: `LinkedChain` carries Kummer/log-shell compatibility as fields;
  distortion 0 is a theorem in that model; M3 drift chain is excluded as not compatible.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1SSIneqDependencyAuditActual

/-- Audit rows: (item, status, source). -/
def ssIneqAuditRows : List (String × String × String) :=
  [ ("SSIneq definition", "(s-1)*|log q| <= log-vol(hull(VC(I)))",
     "Iut/Wall/MultiContainer.lean:88"),
    ("wall equivalence", "PROVED: wallOn_thetaRow_iff / wall3_iff",
     "Iut/ThetaLink/Wall.lean:232,237"),
    ("Step (xi) equivalence", "PROVED: xi_iff_ss (XiPrinciple K <-> SSIneq D)",
     "Iut/LogLink/Thm311.lean:219"),
    ("ABC chain", "CONDITIONAL: Thm311 + XiPrinciple => variant/wall/ClassicalABC",
     "Iut/LogLink/Thm311.lean:43-47"),
    ("SSIneq itself", "NOT proved, NOT refuted in the model (explicit hypothesis)",
     "Iut/LogLink/Thm311.lean:59-67"),
    ("output law", "PROVED in model: ThetaShift identified-copies law; no different law",
     "Iut/LogLink/Thm311.lean:53-65") ]

theorem ssIneqAuditRows_length : ssIneqAuditRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1SSIneqDependencyAuditActual
