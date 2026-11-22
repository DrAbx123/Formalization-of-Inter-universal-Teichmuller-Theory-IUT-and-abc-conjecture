import tmp.sheaf.n8.closure.EtaRssLogShellLine
import tmp.sheaf.n8.closure.EtaValueGroupLineActual

/-!
# Eta comparison map actual (Wave ETA comparison)

The actual Rss carrier EtaRssLogShellLineData X has every field fixed by its
equality fields: shell is the native log-shell, volumeIndex is the production
consumer index, and logVolume is Real.log of that index.  Therefore the carrier
is a subsingleton.

Actual comparison map Rval -> EtaRssLogShellLineData X is the canonical constant
map to etaRssLogShellLineData X.  A nonconstant comparison map, or an
independent etaQ/etaAnab square, is impossible on this carrier: exact no-go by
subsingleton.  No arbitrary map is introduced.

No owner file edited.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaComparisonMapActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C2Native
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual
open LeanFormal.IUT.N8Closure.EtaRssLogShellLine

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual comparison map: canonical constant map to the actual native
log-shell line. -/
noncomputable def etaComparisonMapActual :
    Rval → EtaRssLogShellLineData X :=
  fun _ => etaRssLogShellLineData X

/-- Rss log-shell line data is a subsingleton: its shell, volume index and
log-volume are all fixed by equality fields. -/
theorem etaRssLogShellLineData_subsingleton :
    Subsingleton (EtaRssLogShellLineData X) := by
  constructor
  intro a b
  cases a with
  | mk shell shell_eq volumeIndex volumeIndex_eq logVolume logVolume_eq =>
  cases b with
  | mk shell' shell_eq' volumeIndex' volumeIndex_eq' logVolume' logVolume_eq' =>
  have hshell : shell = shell' := by rw [shell_eq, shell_eq']
  have hvol : volumeIndex = volumeIndex' := by rw [volumeIndex_eq, volumeIndex_eq']
  have hlog : logVolume = logVolume' := by
    rw [logVolume_eq, logVolume_eq', volumeIndex_eq, volumeIndex_eq']
  subst hshell
  subst hvol
  subst hlog
  rfl

/-- Every map from Rval to the actual Rss line is constant. -/
theorem etaComparisonMap_constant
    (f : Rval → EtaRssLogShellLineData X) :
    ∀ a b : Rval, f a = f b :=
  haveI : Subsingleton (EtaRssLogShellLineData X) :=
    etaRssLogShellLineData_subsingleton X
  fun _ _ => Subsingleton.elim _ _

/-- Nonconstant comparison requirement. -/
def EtaComparisonNonconstant
    (f : Rval → EtaRssLogShellLineData X) : Prop :=
  ¬ ∃ c : EtaRssLogShellLineData X, ∀ a : Rval, f a = c

/-- Exact no-go: no nonconstant comparison map exists on the actual Rss line. -/
theorem no_nonconstant_comparison
    (f : Rval → EtaRssLogShellLineData X) :
    ¬ EtaComparisonNonconstant X f := by
  intro h
  apply h
  haveI : Subsingleton (EtaRssLogShellLineData X) :=
    etaRssLogShellLineData_subsingleton X
  exact ⟨etaRssLogShellLineData X, fun _ => Subsingleton.elim _ _⟩

/-- The canonical actual comparison is constant. -/
theorem etaComparisonMapActual_constant :
    ∀ a b : Rval, etaComparisonMapActual X a = etaComparisonMapActual X b :=
  etaComparisonMap_constant X (etaComparisonMapActual X)

/-- etaQ map on the actual carrier: canonical comparison map. -/
def etaQMap : Rval → EtaRssLogShellLineData X :=
  etaComparisonMapActual X

/-- etaAnab map on the actual carrier: canonical comparison map. -/
def etaAnabMap : Rval → EtaRssLogShellLineData X :=
  etaComparisonMapActual X

/-- The etaQ/etaAnab square is actual, but only because both maps are the same
canonical constant map. -/
theorem etaQ_etaAnab_square :
    ∀ a : Rval, etaQMap X a = etaAnabMap X a :=
  fun a => rfl

/-- Exact no-go record: any claim of an independent nonconstant etaQ/etaAnab
comparison on this carrier is impossible. -/
def EtaIndependentComparisonNoGo (X : N8NativeInput l) : Prop :=
  ¬ ∃ f : Rval → EtaRssLogShellLineData X,
      EtaComparisonNonconstant X f

theorem etaIndependentComparison_noGo :
    EtaIndependentComparisonNoGo X := by
  rintro ⟨f, hf⟩
  exact no_nonconstant_comparison X f hf

end LeanFormal.IUT.N8Closure.EtaComparisonMapActual
