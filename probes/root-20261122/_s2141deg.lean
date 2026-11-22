import tmp.sheaf.xif.paper.S2132D5FactorizationActual
open Polynomial
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
example : S2132Factor2.natDegree = 2 := by
  unfold S2132Factor2
  compute_degree!
example : (C (4 : ZMod 29) * S2132Factor10).natDegree = 10 := by
  unfold S2132Factor10
  unfold _root_.f
  compute_degree!
