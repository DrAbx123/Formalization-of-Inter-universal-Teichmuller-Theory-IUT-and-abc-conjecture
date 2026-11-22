import tmp.sheaf.xif.paper.S2229RangeTransitivityActual
open LeanFormal.IUT.XiFPaper.S2229RangeTransitivityActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
example : ZMod S1987Five.value = ZMod 5 := rfl
example (x : ZMod S1987Five.value) : S2229ZModEquiv x = (show ZMod 5 from x) := by
  simp [S2229ZModEquiv]
example (g : GL (Fin 2) (ZMod S1987Five.value)) : (S2229GLMap g : GL2) = (show GL2 from g) := by
  rfl
