/-
S2009 consumer check: the reusable interface of S2009DicksonActual.
-/
import tmp.sheaf.xif.paper.S2009DicksonActual

open LeanFormal.IUT.XiFPaper.S2009DicksonActual

#check @det_surjective
#check @natCard_GL2
#check @pairAct_transitive
#check @cycleType_pairPerm_g102
#check @ten_dvd_natCard_of_mem_cycleType102
#check @no_cycleType102_of_natCard_96
#check @no_cycleType102_of_natCard_48
#check @S2009DicksonTransitiveClassification
#check @S2009ExactFirstMissing
#check @largeImage_of_dickson

example : Function.Surjective (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod 5)) :=
  det_surjective

example : Nat.card (GL (Fin 2) (ZMod 5)) = 480 := natCard_GL2

example : S2009DicksonTransitiveClassification →
    ∀ H : Subgroup (GL (Fin 2) (ZMod 5)), DetSurjectiveOn H → PairTransitive H →
      HasCycleType102 H → H = ⊤ :=
  fun hD H hdet htrans h102 => largeImage_of_dickson hD H hdet htrans h102
