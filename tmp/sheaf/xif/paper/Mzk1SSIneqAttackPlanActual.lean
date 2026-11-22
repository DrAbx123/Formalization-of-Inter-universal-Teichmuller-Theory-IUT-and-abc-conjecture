/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic

/-! # A741 hull: attack plan for `SSIneq D` (Scholze-Stix inequality)

Read-only analysis of lana `Iut/Wall/*.lean` (rev main).  Target:

  `SSIneq D := (sFactor (nC D) - 1) * D.qPilot.absLogQ <= logVol D (hullOf D (vcI D))`

lana proves `Wall D (idAlgOn D sigma) <-> SSIneq D` (Constraints.lean:304) and
constructs `idAlgOn` completely (Constraints.lean:272-280).  This file records the
exact definitions/lemmas, the reduction of SSIneq to an Ind3-volume existence
statement, and the conclusion that the remaining input is exactly SSIneq itself
(the analytic lower bound on the hull log-volume) -- not a missing eta-algorithm
field for `idAlgOn`.

The real-number skeleton below is proved unconditionally (pure algebra); it does
not assume SSIneq.  No RETRACTED `hfull`/N-scaling file is referenced. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1SSIneqAttackPlanActual

/-- `SSIneq` as a pure real inequality `(s-1)*|log q| <= hullVol`. -/
def SSIneqShape (s absLogQ hullVol : Real) : Prop := (s - 1) * absLogQ <= hullVol

/-- The `LGP`-volume form: `SSIneq` is equivalent to the lower bound
`-|log q| <= logVol(LGP.S)` for `S = hull(VC(I))`, where
`logVol(LGP.S) = -s*|log q| + logVol(S)`. -/
theorem ssiIneqShape_iff_lgp_bound (s absLogQ hullVol L : Real)
    (hL : L = -s * absLogQ + hullVol) :
    SSIneqShape s absLogQ hullVol <-> -absLogQ <= L := by
  unfold SSIneqShape
  constructor <;> intro h <;> linarith

/-- `SSIneq` is equivalent to the existence of an `Ind3`-choice of log-volume
`(s-1)*|log q|` (the content of lana `exists_ind3_logVol_iff`). -/
theorem ssiIneqShape_iff_exists_volume (s absLogQ hullVol : Real) :
    SSIneqShape s absLogQ hullVol <->
      exists x : Real, x = (s - 1) * absLogQ and x <= hullVol := by
  unfold SSIneqShape
  constructor
  · intro h
    exact ⟨(s - 1) * absLogQ, rfl, h⟩
  · rintro ⟨x, rfl, h⟩
    exact h

/-- If an `Ind3`-choice has log-volume exactly `(s-1)*|log q|`, then `SSIneq` holds. -/
theorem ssiIneqShape_of_ind3_volume {s absLogQ hullVol x : Real}
    (hx : x = (s - 1) * absLogQ) (hle : x <= hullVol) :
    SSIneqShape s absLogQ hullVol :=
  by rw [SSIneqShape, <- hx]; exact hle

/-- If `LGP.S` satisfies `-|log q| <= logVol(LGP.S)` and the LGP volume law, then `SSIneq`. -/
theorem ssiIneqShape_of_lgp_bound {s absLogQ hullVol L : Real}
    (hL : L = -s * absLogQ + hullVol) (h : -absLogQ <= L) :
    SSIneqShape s absLogQ hullVol :=
  (ssiIneqShape_iff_lgp_bound s absLogQ hullVol L hL).mpr h

/-! ## Audit tables (strings, no named structure) -/

/-- Exact definitions used by the attack. -/
def ssiDefinitionRows : List (String × String × String) :=
  [ ("sFactor", "sFactor n = (sum_{j<n} (j+1)^2)/n = (n+1)(2n+1)/6 for n>0", "Pilots.lean:55-67"),
    ("nC", "nC D = (D.ell - 1)/2 = ell*", "Rss.lean:303"),
    ("lgp", "lgp D S = fun i => lgpAt D i (S i); lgpAt multiplies finite packets by LGP element q_{v_j}^{j^2}", "IdentifiedCopies.lean:145-169"),
    ("lgp_eq_pow", "lgp D S = pow D (fun _ => 1) (labOne D) S", "QPilotRegion.lean:139"),
    ("vcI", "vcI D : Region D = vcIAt D (the log-shell container VC(I))", "Ind3.lean:123"),
    ("hullOf", "hullOf D U = (LocalTheory.hull D.placeSect (nC D)).hullFamily U", "Rss.lean:328"),
    ("logVol", "logVol D U = (LocalTheory.vol D.placeSect (nC D)).processionVol U", "Rss.lean:324"),
    ("etaQ", "etaQ D : (qVal D.bpsDegrees).C ->+[R] R, the pointed map of the q-pilot (log-volume of qRegion)", "Rss.lean:501-505"),
    ("qRegion", "qRegion D = pow D (fun _ => 1) (labOne D) (integralRegion D)", "QPilotRegion.lean:314"),
    ("IsAdelic", "IsAdelic D U = forall i, (hull).IsAdmissible (U i)", "Rss.lean:319"),
    ("InHullOfImage", "InHullOfImage D U = exists l, forall i, U i <= hullOf D (thetaImage D l) i", "Rss.lean:338"),
    ("Ind3", "Ind3 D = {S : Region D // IsAdelic D S and forall i, S i <= hullOf D (vcI D) i}", "Ind3.lean:213") ]

theorem ssiDefinitionRows_length : ssiDefinitionRows.length = 12 := rfl

/-- Proved lemmas relevant to the attack. -/
def ssiLemmaRows : List (String × String × String) :=
  [ ("isAdelic_lgp", "IsAdelic D S -> IsAdelic D (lgp D S)", "IdentifiedCopies.lean:183"),
    ("inHullOfImage_lgp", "S : Ind3 D -> InHullOfImage D (lgp D S.1)", "IdentifiedCopies.lean:229"),
    ("logVol_lgp", "IsAdelic D S -> logVol D (lgp D S) = logVol D (lgp D (integralRegion D)) + logVol D S", "IdentifiedCopies.lean:281"),
    ("logVol_lgp_integral", "logVol D (lgp D (integralRegion D)) = -(sFactor (nC D) * D.qPilot.absLogQ)", "IdentifiedCopies.lean:444"),
    ("logVol_le_vcI", "S : Ind3 D -> logVol D S.1 <= logVol D (hullOf D (vcI D))", "Ind3.lean:244"),
    ("exists_ind3_logVol_iff", "(exists S : Ind3 D, logVol D S.1 = x) <-> x <= logVol D (hullOf D (vcI D))", "Ind3.lean:253"),
    ("logVol_qRegion", "logVol D (qRegion D) = (concreteVariantData D).qPilot.lhs = -D.qPilot.absLogQ", "QPilotRegion.lean:321"),
    ("logVol_le_rhs", "IsAdelic U -> InHullOfImage U -> logVol D U <= (concreteVariantData D).rhsData.rhs", "Rss.lean:374"),
    ("wall_idAlgOn_iff", "Wall D (idAlgOn D sigma) <-> SSIneq D", "Constraints.lean:304-308"),
    ("wall_idAlg_iff", "Wall D (idAlg D) <-> SSIneq D", "IdentifiedCopies.lean:488-500"),
    ("idAlgOn fields", "model trivialGM, Side = sigma, out iota S = lgp D S.1, realisation = (isAdelic_lgp, inHullOfImage_lgp)", "Constraints.lean:272-280") ]

theorem ssiLemmaRows_length : ssiLemmaRows.length = 11 := rfl

/-- The reduction/attack rows. -/
def attackGapRows : List (String × String × String) :=
  [ ("step 1", "Wall D (idAlgOn D sigma) <-> SSIneq D (lana wall_idAlgOn_iff)", "equivalence; no eta-algorithm input"),
    ("step 2", "Wall needs exists iota S, etaAnab iota S = etaQ D; for idAlgOn, out iota S = lgp D S.1", "Fields of idAlgOn fully constructed"),
    ("step 3", "etaAnab_eq_etaQ_iff: need logVol D (lgp D S) = -D.qPilot.absLogQ", "ValBPS.eta_eq_eta_iff / EtaAlg.lean:149-153"),
    ("step 4", "logVol D (lgp D S) = -sFactor(nC) * absLogQ + logVol D S", "logVol_lgp + logVol_lgp_integral"),
    ("step 5", "need S : Ind3 D with logVol D S = (sFactor(nC)-1)*absLogQ", "first-order equivalence of step 4"),
    ("step 6", "such S exists iff (sFactor(nC)-1)*absLogQ <= logVol D (hullOf D (vcI D))", "exists_ind3_logVol_iff"),
    ("step 7", "step 6 is exactly SSIneq D: the chain is CIRCULAR; it does not prove SSIneq", "must not be presented as proof"),
    ("unique gap", "SSIneq D itself: analytic lower bound on logVol(hull(VC(I)))", "lana MultiContainer.lean:83-87: neither SSIneq nor its negation is proved") ]

theorem attackGapRows_length : attackGapRows.length = 8 := rfl

/-- Missing objects, if one insists on the eta-algorithm route (not needed for idAlgOn). -/
def missingObjectRows : List (String × String × String) :=
  [ ("idAlgOn attack", "No missing EtaAlg fields: model/Side/etUnit/out/ind12/etUnitOnly/realisation all constructed in lana", "Constraints.lean:272-280"),
    ("purely analytic input", "lower bound logVol(hull(VC(I))) >= (s-1)*|log q|", "NOT in lana; lana says SSIneq unproved"),
    ("if using a general EtaAlg", "out field (eta-algorithm), realisation (T3), ind12_acts_on_S (T1), etUnitOnly (T2)", "LANA report calls the wall step not reconstructible; no repo construction"),
    ("our repo", "no lana InitialThetaData/EtaAlg/Wall/SSIneq instance; no analytic lower bound for hull(VC(I))", "INTEGRITY; ABC gate NOT passed") ]

theorem missingObjectRows_length : missingObjectRows.length = 4 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1SSIneqAttackPlanActual.ssiIneqShape_iff_lgp_bound
#print axioms LeanFormal.IUT.XiFPaper.Mzk1SSIneqAttackPlanActual.ssiIneqShape_iff_exists_volume
#print axioms LeanFormal.IUT.XiFPaper.Mzk1SSIneqAttackPlanActual.ssiIneqShape_of_ind3_volume

end LeanFormal.IUT.XiFPaper.Mzk1SSIneqAttackPlanActual