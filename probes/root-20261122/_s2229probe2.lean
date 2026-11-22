import tmp.sheaf.xif.paper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
noncomputable section
example : S1987Five.value = 5 := rfl
noncomputable def E : ZMod S1987Five.value ≃+* ZMod 5 := ZMod.ringEquivCongr (by rfl : S1987Five.value = 5)
noncomputable def GLM : GL (Fin 2) (ZMod S1987Five.value) →* GL2 := Matrix.GeneralLinearGroup.map E.toRingHom
