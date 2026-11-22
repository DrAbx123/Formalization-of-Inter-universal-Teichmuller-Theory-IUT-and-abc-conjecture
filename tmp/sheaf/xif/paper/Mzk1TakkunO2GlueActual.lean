import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import tmp.sheaf.takkun.IutLean.LogTheta.LogShell

/-!
# O2 glue: our reduced source log-shell carrier -> Takkun LogShell / LogLink

Reuses the green Takkun modules `LogTheta/LogShell` (`LogShell`, `LogLink` and
their proved laws) together with our real `SourceLogShellDatum` reduction of
IUT III Def 1.1(i).  The carrier of the Takkun shell is our log-coordinate
field `K`; the Takkun log-link comes from our monoid hom
`Units ->* Multiplicative K`, viewed additively.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1TakkunO2GlueActual

open LeanFormal.IUT

noncomputable section

universe u

/-- Takkun `LogShell` whose carrier is the log-coordinate field of our
`SourceLogShellDatum` (IUT III Def 1.1(i) reduced core). -/
def takkunLogShellOfSource (D : SourceLogShellDatum.{u}) :
    _root_.IUT.LogTheta.LogShell.{u} where
  carrier := D.K
  addCommGroup := inferInstance

@[simp] theorem takkunLogShellOfSource_carrier (D : SourceLogShellDatum.{u}) :
    (takkunLogShellOfSource D).carrier = D.K := rfl

/-- Takkun `LogLink` built from the actual `logMap : Units ->* Multiplicative K`
of `SourceLogShellDatum`, viewed additively (`Additive U ->+ K`). -/
def takkunLogLinkOfSource (D : SourceLogShellDatum.{u}) :
    _root_.IUT.LogTheta.LogLink D.Units (takkunLogShellOfSource D) where
  logMap :=
    { toFun := fun a => (D.logMap (Additive.toMul a)).toAdd
      map_zero' := by
        change (D.logMap (Additive.toMul (0 : Additive D.Units))).toAdd = 0
        change (D.logMap 1).toAdd = 0
        rw [map_one]
        rfl
      map_add' := by
        intro a b
        change (D.logMap (Additive.toMul (a + b))).toAdd =
          (D.logMap (Additive.toMul a)).toAdd + (D.logMap (Additive.toMul b)).toAdd
        change (D.logMap (Additive.toMul a * Additive.toMul b)).toAdd =
          (D.logMap (Additive.toMul a)).toAdd + (D.logMap (Additive.toMul b)).toAdd
        rw [map_mul]
        rfl }

@[simp] theorem takkunLogLinkOfSource_logMap_one (D : SourceLogShellDatum.{u}) :
    (takkunLogLinkOfSource D).logMap (Additive.ofMul 1) = 0 :=
  _root_.IUT.LogTheta.LogLink.logMap_one _

/-- Bundled O2 data: actual log-shell carrier plus actual log-link, both built
from source data (no parameters are placeholders). -/
structure O2Data (D : SourceLogShellDatum.{u}) where
  shell : _root_.IUT.LogTheta.LogShell.{u}
  link : _root_.IUT.LogTheta.LogLink D.Units shell

def o2DataOfSource (D : SourceLogShellDatum.{u}) : O2Data D :=
  { shell := takkunLogShellOfSource D, link := takkunLogLinkOfSource D }

@[simp] theorem o2DataOfSource_shell (D : SourceLogShellDatum.{u}) :
    (o2DataOfSource D).shell = takkunLogShellOfSource D := rfl

theorem o2DataOfSource_link_one (D : SourceLogShellDatum.{u}) :
    (o2DataOfSource D).link.logMap (Additive.ofMul 1) = 0 :=
  _root_.IUT.LogTheta.LogLink.logMap_one _

end

end LeanFormal.IUT.XiFPaper.Mzk1TakkunO2GlueActual
