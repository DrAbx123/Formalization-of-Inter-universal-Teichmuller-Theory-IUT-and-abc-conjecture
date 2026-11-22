import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
example : ZMod S1987Five.value = ZMod 5 := rfl
example : GL (Fin 2) (ZMod S1987Five.value) = GL2 := rfl
#check S1987Five
#check S1987Five.value
