import tmp.sheaf.xif.paper.S2605LiftSLActual
open LeanFormal.IUT.XiFPaper.S2605LiftSLActual
example : (algebraMap Sb Lb) = liftSL := rfl
example (s : Sb) (t : Lb) : s • t = algebraMap Sb Lb s * t := Algebra.smul_def s t
