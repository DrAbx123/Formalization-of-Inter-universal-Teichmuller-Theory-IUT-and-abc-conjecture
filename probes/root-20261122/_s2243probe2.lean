import tmp.sheaf.xif.paper.S2229RangeTransitivityActual
open LeanFormal.IUT.XiFPaper.S2229RangeTransitivityActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
example : S2229GLMap = MonoidHom.id (GL (Fin 2) (ZMod S1987Five.value)) := by
  ext g
  rfl
example (H : Subgroup GL2) : H.map (MonoidHom.id GL2) = H := by
  rw [Subgroup.map_id]
