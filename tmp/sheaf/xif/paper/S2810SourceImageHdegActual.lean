import tmp.sheaf.xif.paper.S1666SourceImageRealizationActual
import tmp.sheaf.xif.paper.S2600LogShellRealizationActual
import tmp.sheaf.xif.paper.S2601LogShellPortActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1666SourceImageRealizationActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2810SourceImageHdegActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {v : V}

/-- `hdeg` is stronger than `SourceImageRealization.degree_of_q`: it gives
degree faithfulness at every real `b`, in particular at `b = log q`. -/
theorem S2810_hdeg_implies_degree_of_q
    (R : I.SourceImageRealization v)
    (hdeg : forall b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    I.logDegreeAt 0 0 v
        (R.posRealAction (Multiplicative.ofAdd
          (Real.log ((I.theaterAt 0 0).thetaPacket.q)))) =
      Real.log ((I.theaterAt 0 0).thetaPacket.q) :=
  hdeg _

/-- The actual S1666 source-Haar realization has constant positive-real action
`b |-> 1`; its log-degree is therefore `0` at every `b`. -/
theorem S2810_sourceHaarActual_logDegree_eq_zero
    (S : SourceDefinition31Data.{ua} l) (b : Real) :
    (sourceHaarActualOriginalInput (l := l) S).logDegreeAt 0 0 ()
        ((sourceHaarActualImageRealization (l := l) S).posRealAction
          (Multiplicative.ofAdd b)) = 0 := by
  rw [show (sourceHaarActualImageRealization (l := l) S).posRealAction
        (Multiplicative.ofAdd b) = 1 from rfl]
  exact (sourceHaarActualOriginalInput (l := l) S).logDegreeAt_one 0 0 ()

/-- Exact blocker: the existing actual source-Haar realization cannot be
upgraded to `SourceImageRealizationLogShell` by proving `hdeg`, because its
action is constant and every degree is zero.  In particular `hdeg 1` would
force `0 = 1`. -/
theorem S2810_sourceHaarActual_hdeg_impossible
    (S : SourceDefinition31Data.{ua} l) :
    ¬ (forall b : Real,
      (sourceHaarActualOriginalInput (l := l) S).logDegreeAt 0 0 ()
        ((sourceHaarActualImageRealization (l := l) S).posRealAction
          (Multiplicative.ofAdd b)) = b) := by
  intro h
  have h1 := h 1
  have hzero : (sourceHaarActualOriginalInput (l := l) S).logDegreeAt 0 0 ()
      ((sourceHaarActualImageRealization (l := l) S).posRealAction
        (Multiplicative.ofAdd (1 : Real))) = 0 :=
    S2810_sourceHaarActual_logDegree_eq_zero (l := l) S 1
  rw [hzero] at h1
  norm_num at h1

#check S2810_hdeg_implies_degree_of_q
#check S2810_sourceHaarActual_logDegree_eq_zero
#check S2810_sourceHaarActual_hdeg_impossible
#print axioms S2810_sourceHaarActual_hdeg_impossible

end LeanFormal.IUT.XiFPaper.S2810SourceImageHdegActual
end
