import tmp.sheaf.xif.paper.Mzk1P58iiCMLFActual

/-!
# Mzk1CMLFConsumerChainActual — consumer theorems for the concrete CMLF model
(Mzk1P58iiCMLFActual, EXIT0). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1CMLFConsumerChainActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1P58iiCMLFActual

universe u

/-- Consumer: composition acts on the field map by composition. -/
theorem consumer_comp_mapK {D E F : SourceLogShellDatum.{u}} (f : CMLFHom D E)
    (g : CMLFHom E F) : (f.comp g).mapK = g.mapK.comp f.mapK :=
  CMLFHom.comp_mapK f g

/-- Consumer: composition acts on the unit map by composition. -/
theorem consumer_comp_mapUnits {D E F : SourceLogShellDatum.{u}} (f : CMLFHom D E)
    (g : CMLFHom E F) : (f.comp g).mapUnits = g.mapUnits.comp f.mapUnits :=
  CMLFHom.comp_mapUnits f g

/-- Consumer: the identity field map is the identity. -/
theorem consumer_id_mapK (D : SourceLogShellDatum.{u}) :
    (CMLFHom.id D).mapK = RingHom.id D.K := rfl

/-- Consumer: p* is positive for source log-shell data. -/
theorem consumer_pStar_pos (D : SourceLogShellDatum.{u}) : 0 < D.pStar :=
  D.pStar_pos

/-- Consumer: the CMLF model row record has six rows. -/
theorem consumer_cmlf_rows : cmlfModelRows.length = 6 :=
  cmlfModelRows_length

#check consumer_comp_mapK
#check consumer_comp_mapUnits
#check consumer_id_mapK
#check consumer_pStar_pos
#check consumer_cmlf_rows

end LeanFormal.IUT.XiFPaper.Mzk1CMLFConsumerChainActual
end
