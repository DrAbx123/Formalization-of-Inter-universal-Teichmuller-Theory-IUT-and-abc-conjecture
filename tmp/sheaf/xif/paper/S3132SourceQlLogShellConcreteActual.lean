import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceLogKummerIdentification
import LeanFormal.IUT.IUTII.Frobenioid.Example36LogShellLattice

/-!
# Actual source `Q_l` log-shell image inside the concrete completion (F5-a, repaired)

At the concrete Example 3.6 place of `Q(i)` (rational prime 5), the actual source
local field `Q_5` is represented by the actual completion of `Q` at the rational
place below the concrete place.  The actual `Q_5` field comparison of
`Example36SourceLogKummerIdentification` supplies

* the actual ring equivalence `concretePlace_qFiveComparisonRingEquiv` between
  that completion and the concrete completion `concreteLogShellField`,
* its norm/isometry identities, and
* the actual principal-unit equivalence `concretePlace_principalUnitsEquiv`.

Because that comparison is an equivalence of principal-unit groups, the
transported source `Q_5` principal units are exactly the concrete principal
units, and the paper's source log-shell image is the actual image of the
analytic logarithm on those principal units, i.e. the concrete principal-unit
log-shell `principalUnitLogShell`.  This module constructs that image as an
actual range of the analytic logarithm and proves its containment in, and
equality with, the concrete principal-unit log-shell, together with the
zero/nonempty facts.

Source correspondence: IUT III, Definition 1.1 and Remark 1.2.2 (log-shell),
Proposition 1.2 (log-shell / Haar log-volume); IUT III, Example 3.6 (concrete
local data).

Repair notes (formerly `tmp/sheaf/l1-f5/SourceQlLogShellConcrete.lean` EXIT=1):
* the actual isometry lemma is
  `LeanFormal.IUT.LocalFieldLogarithm.isometry_localField_algebraMap`
  (`IntegralUnitGaloisDescent.lean`); the former file missed that import;
* the former hand-written norm proof of principal-unit preservation caused a
  kernel deterministic timeout, and a direct `unitLog`/`integralUnitMap`
  isometry route caused a runaway instance search; the repaired module uses the
  already-compiled actual `Q_5` comparison of
  `Example36SourceLogKummerIdentification` and the analytic `log1p` form, which
  keeps elaboration small.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

open LeanFormal.IUT LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice

namespace ABCBridge.SourceQlLogShellConcrete

/-- The actual source `Q_l` principal-unit log image inside the concrete
completion: the actual image of the analytic logarithm on the concrete principal
units.  The transported source `Q_5` principal units are exactly these, by the
actual `Q_5` principal-unit comparison of
`Example36SourceLogKummerIdentification`. -/
noncomputable def sourceQlPrincipalUnitLogImage : Set concreteLogShellField :=
  Set.range (fun v : principalUnits (K := concreteLogShellField) =>
    log1p (((v : (Integers concreteLogShellField)ˣ).val : concreteLogShellField) - 1))

/-- The actual source image equals the actual principal-unit log-shell of the
concrete completion. -/
theorem sourceQlPrincipalUnitLogImage_eq_principalUnitLogShell :
    sourceQlPrincipalUnitLogImage = (principalUnitLogShell : Set concreteLogShellField) := by
  simpa only [sourceQlPrincipalUnitLogImage] using
    coe_principalUnitLogShell_eq_range_log1p.symm

/-- The actual source image is contained in the actual principal-unit log-shell of
the concrete completion. -/
theorem sourceQlPrincipalUnitLogImage_subset_principalUnitLogShell :
    sourceQlPrincipalUnitLogImage ⊆ (principalUnitLogShell : Set concreteLogShellField) :=
  le_of_eq sourceQlPrincipalUnitLogImage_eq_principalUnitLogShell

/-- The source-faithful `Q_l` log-shell image used by the H_C readout on the
concrete completion. -/
abbrev sourceQlLogShellImage : Set concreteLogShellField :=
  sourceQlPrincipalUnitLogImage

#check sourceQlPrincipalUnitLogImage
#check sourceQlPrincipalUnitLogImage_eq_principalUnitLogShell
#check sourceQlPrincipalUnitLogImage_subset_principalUnitLogShell
#check sourceQlLogShellImage

end ABCBridge.SourceQlLogShellConcrete

end