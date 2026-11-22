import tmp.sheaf.xif.paper.S2735QPilotLineBundleActual
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual
import tmp.sheaf.xif.paper.ArithmeticLineBundleActual
import Mathlib.RingTheory.DedekindDomain.Different
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
namespace LeanFormal.IUT.XiFPaper.S2990Probe
abbrev R : Type := SourceOK (A := S2735Arithmetic S2771FiveLabel)
#check differentIdeal
#check conductor
noncomputable def S2990D : Real :=
  (Ideal.absNorm (differentIdeal ℤ R) : Real)
#check S2990D
end LeanFormal.IUT.XiFPaper.S2990Probe
end