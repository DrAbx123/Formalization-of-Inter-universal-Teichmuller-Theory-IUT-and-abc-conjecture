import tmp.sheaf.xif.paper.S3136BDClassChainToolActual
import tmp.sheaf.xif.paper.S3136GenEllReductionShapeActual

/-! # Stage-4 host: paper-input statement hooks (definitional shapes)

Source anchors: IUT IV, Theorem A p.93-112 and Corollary 2.3 p.3117-3128
(inequality of BD-classes ht_omega_X(D) <~ (1+eps)(log-diff_X + log-cond_D) on
U_X(Q)<=d); [GenEll] Theorem 2.1 p.615 (equivalence of the general statement
and the compactly bounded statement); [GenEll] Proposition 1.4, (i), (iii)
(height algebra and BD-class invariance).

CONSUMER: mainline's IUT IV statement skeleton. This file records the exact
definitional SHAPES of the endpoint statements as Lean propositions built from
the class A BD-class tool (IsBDLe), so the skeleton can plug them as statement
slots without asserting them. No analytic inequality is proved.

LABEL: statement hooks (definitional shapes, class A). Registry frozen; new file
only. -/

namespace LeanFormal.IUT.XiFPaper.S3136PaperInputStatementHooksActual

open LeanFormal.IUT.XiFPaper.S3136BDClassChainToolActual
open LeanFormal.IUT.XiFPaper.S3136GenEllReductionShapeActual

variable {α : Type*}

/-- The IUT IV Theorem A / Corollary 2.3 inequality shape: the canonical height is
BD-dominated by (1+eps)(log-different + log-conductor) on the d-bounded set. -/
def LGPTheoremAShape (F : Set α) (htHgF logDiff logCond : α → ℝ) (eps : ℝ) : Prop :=
  IsBDLe htHgF (fun x => (1 + eps) * (logDiff x + logCond x)) F

/-- The [GenEll] Theorem 2.1 general-statement shape. -/
def LGPGenEllGeneralShape (F : Set α) (htHgF logDiff logCond : α → ℝ)
    (eps : ℝ) : Prop :=
  LGPTheoremAShape F htHgF logDiff logCond eps

/-- The [GenEll] Theorem 2.1 compactly-bounded-statement shape (same inequality
restricted to the compactly bounded set K_V cap U(Q)<=d). -/
def LGPGenEllCompactlyBoundedShape (KV : Set α) (htHgF logDiff logCond : α → ℝ)
    (eps : ℝ) : Prop :=
  LGPTheoremAShape KV htHgF logDiff logCond eps

/-- The reduction hook: from the equivalence and the compactly bounded statement,
the general statement follows. -/
theorem lgpTheoremA_of_compactlyBounded {generalStatement compactlyBoundedStatement : Prop}
    (h : LGPGenEllEquivalence generalStatement compactlyBoundedStatement)
    (hb : compactlyBoundedStatement) :
    generalStatement :=
  h.mpr hb

#check LGPTheoremAShape
#check LGPGenEllGeneralShape
#check LGPGenEllCompactlyBoundedShape
#check lgpTheoremA_of_compactlyBounded

end LeanFormal.IUT.XiFPaper.S3136PaperInputStatementHooksActual