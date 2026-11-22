import tmp.sheaf.xif.paper.GenEll04Prop17Actual
import tmp.sheaf.xif.paper.GenEll02bProofActual
noncomputable section
open LeanFormal.IUT
namespace LeanFormal.IUT.XiFPaper.GenEll04bChainActual

open LeanFormal.IUT.XiFPaper.S3136BDClassChainToolActual
open LeanFormal.IUT.XiFPaper.GenEll04Prop17Actual

/-- **Prop 1.7(i) assembled from its two BD inputs** (the paper's elementary different
theory supplies the first and the (1-1/e) bound the second; the tower/different
estimates DifferentTowerEstimate.iutIVProp13i_normalizedDifferent_ge and
DifferentDegreeUpperBound are the reusable IUT-side anchors). -/
theorem prop17_logDiff_inequality_of_inputs {Y : Type} {UYQ : Set Y}
    {logCondE logCondD logDiffY logDiffZ : Y → Real} {e : Nat}
    (h1 : IsBDLe (fun y => logDiffY y - logDiffZ y)
      (fun y => logCondE y - logCondD y) UYQ)
    (h2 : IsBDLe (fun y => ((1 : Real) - 1 / (e : Real)) * logCondE y)
      (fun y => logDiffY y - logDiffZ y) UYQ) :
    Prop17LogDiffInequality UYQ logCondE logCondD logDiffY logDiffZ e :=
  ⟨h1, h2⟩

/-- Chaining consequence: log-cond_E - log-cond_D is BD-bounded by the scaled
log-cond_E via the two-step Prop 1.7 chain. -/
theorem prop17_chain {Y : Type} {UYQ : Set Y}
    {logCondE logCondD logDiffY logDiffZ : Y → Real} {e : Nat}
    (h1 : IsBDLe (fun y => logDiffY y - logDiffZ y)
      (fun y => logCondE y - logCondD y) UYQ)
    (h2 : IsBDLe (fun y => ((1 : Real) - 1 / (e : Real)) * logCondE y)
      (fun y => logDiffY y - logDiffZ y) UYQ) :
    IsBDLe (fun y => ((1 : Real) - 1 / (e : Real)) * logCondE y)
      (fun y => logCondE y - logCondD y) UYQ :=
  isBDLe_trans h2 h1

def s3135Prop17ProofCitations : List (String × String) :=
  [ ("Prop 1.7(i)", "corpus 565-602: separated wildly/tamely; wild claim p^n O_L in different via Kummer theory; bounded over Sigma; our assembly takes the two BD inputs as the elementary different-theory outputs"),
    ("Prop 1.7(ii)", "corpus 602-604: Riemann-Hurwitz"),
    ("IUT-side reusable anchors", "IUTIV/Estimates/DifferentTowerEstimate.lean iutIVProp13i_normalizedDifferent_ge; DifferentDegreeUpperBound.lean") ]

theorem s3135Prop17ProofCitations_length : s3135Prop17ProofCitations.length = 3 := rfl

#check prop17_logDiff_inequality_of_inputs
#check prop17_chain
end LeanFormal.IUT.XiFPaper.GenEll04bChainActual
end
