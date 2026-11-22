import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.Audit.Status

/-!
# S3137: actual Theta x mu LGP-link data relative to the full log-link

IUT III, Definition 3.8, (ii)--(iii) (pp. 112--114), and Remark 1.4.1, (ii)
(pp. 46--47): the horizontal arrow of the LGP-Gaussian log-theta-lattice from
(n,m) to (n+1,m) is the Theta x mu LGP-link *relative to the full log-link*
from (n,m-1) to (n,m).  The Theta-pilot object sits at (0,0) and the q-pilot
object at (1,0) [Definition 3.8, (i), p. 112]; the log-shell/Theta-pilot
comparison therefore lives on the square (0,0) -> (1,0) -> (1,1) and
(0,0) -> (0,1) -> (1,1), where the horizontal arrow at (0,1) is relative to
the log-link (0,0) -> (0,1).

From the actual source input this file constructs the actual preceding full
log-link and LGP arrow with the structure ActualLGPRelativeArrow, the
value-group/unit-group data of the actual LGP arrow (actual isomorphisms of the
value monoid, Galois group and unit group with degree/projection/action
compatibility, taken from the source F-prime-strip link), and the two
composites of the (0,0)--(1,1) intertwining square.  The exact source gap of
Definition 3.8, (ii) -- no F^LGP x mu-prime-strip carrier and no full
poly-isomorphism -- is recorded as a pending Audit obligation, not as a
milestone.  No arbitrary carrier, no True/PUnit, no sorry, no axiom.
WRITE-ONLY.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137ThetaXMuLGPRelativeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Audit

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. Source positions of the pilots and of the comparison -/

def thetaPilotPosition : SourceTheorem311Index := (0, 0)

def qPilotPosition : SourceTheorem311Index := (1, 0)

def logLinkTargetPosition : SourceTheorem311Index := (0, 1)

def comparisonPosition : SourceTheorem311Index := (1, 1)

theorem qPilot_eq_horizontalShift_thetaPilot :
    horizontalIndex thetaPilotPosition = qPilotPosition := rfl

theorem comparison_square_positions :
    verticalIndex qPilotPosition = comparisonPosition ∧
      horizontalIndex logLinkTargetPosition = comparisonPosition :=
  ⟨rfl, rfl⟩

/-! ## 2. The actual LGP arrow relative to the preceding full log-link -/

/-- The actual full log-link ending at the node (n,m). -/
def actualPrecedingLogLink (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n m : Int) : HodgeTheaterLink (I.theaterAt n (m - 1)) (I.theaterAt n m) :=
  I.linkAt n (m - 1) n m

/-- The actual horizontal Theta x mu LGP arrow from (n,m) to (n+1,m). -/
def actualThetaXMuLGPArrow (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n m : Int) : HodgeTheaterLink (I.theaterAt n m) (I.theaterAt (n + 1) m) :=
  I.linkAt n m (n + 1) m

/-- The data of the horizontal LGP arrow at (n,m) relative to the full log-link
ending at (n,m) (IUT III, Definition 3.8, (iii), pp. 113--114). -/
structure ActualLGPRelativeArrow (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n m : Int) where
  logLink : HodgeTheaterLink (I.theaterAt n (m - 1)) (I.theaterAt n m)
  lgpLink : HodgeTheaterLink (I.theaterAt n m) (I.theaterAt (n + 1) m)
  logLink_eq : logLink = I.linkAt n (m - 1) n m
  lgpLink_eq : lgpLink = I.linkAt n m (n + 1) m

noncomputable def actualLGPRelativeArrow
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    ActualLGPRelativeArrow I n m where
  logLink := I.linkAt n (m - 1) n m
  lgpLink := I.linkAt n m (n + 1) m
  logLink_eq := rfl
  lgpLink_eq := rfl

/-- Definition 3.8, (iii): at (0,1) the horizontal LGP arrow is relative to the
actual log-link (0,0) -> (0,1); the composite log-then-LGP is the source link. -/
theorem lgpAt01_relative_to_logLink (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    HodgeTheaterLink.trans (actualPrecedingLogLink I 0 1)
        (actualThetaXMuLGPArrow I 0 1) =
      I.linkAt 0 0 1 1 :=
  I.linkAt_trans 0 0 0 1 1 1

/-- The (0,0) -> (0,1) -> (1,1) composite of the intertwining square. -/
def logThenLGP (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    HodgeTheaterLink (I.theaterAt 0 0) (I.theaterAt 1 1) :=
  HodgeTheaterLink.trans (I.linkAt 0 0 0 1) (I.linkAt 0 1 1 1)

/-- The (0,0) -> (1,0) -> (1,1) composite of the intertwining square. -/
def lgpThenLog (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    HodgeTheaterLink (I.theaterAt 0 0) (I.theaterAt 1 1) :=
  HodgeTheaterLink.trans (I.linkAt 0 0 1 0) (I.linkAt 1 0 1 1)

theorem logThenLGP_eq (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    logThenLGP I = I.linkAt 0 0 1 1 :=
  I.linkAt_trans 0 0 0 1 1 1

theorem lgpThenLog_eq (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    lgpThenLog I = I.linkAt 0 0 1 1 :=
  I.linkAt_trans 0 0 1 0 1 1

theorem intertwining_square_eq (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    logThenLGP I = lgpThenLog I := by
  rw [logThenLGP_eq, lgpThenLog_eq]

/-! ## 3. Value-group and unit-group data of the actual LGP arrow -/

/-- The value-group and unit-group data of the actual horizontal LGP arrow:
actual isomorphisms of the value monoid, Galois group and unit group, with
degree, projection and action compatibility.  Every field is a field of the
actual source F-prime-strip link. -/
structure LGPPolyIsoValueUnitData (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n m : Int) where
  valueIso : ∀ v, (I.primeStripAt n m).Mon v ≃* (I.primeStripAt (n + 1) m).Mon v
  galoisIso : ∀ v, (I.primeStripAt n m).toDPrimeStrip.Pi v ≃*
    (I.primeStripAt (n + 1) m).toDPrimeStrip.Pi v
  unitIso : ∀ v, (I.primeStripAt n m).G v ≃* (I.primeStripAt (n + 1) m).G v
  degree_compat : ∀ v x,
    (I.primeStripAt (n + 1) m).degree v (valueIso v x) =
      (I.primeStripAt n m).degree v x
  proj_compat : ∀ v,
    ((I.primeStripAt (n + 1) m).proj v).comp (galoisIso v).toMonoidHom =
      (unitIso v).toMonoidHom.comp ((I.primeStripAt n m).proj v)
  action_compat : ∀ v g x,
    valueIso v ((I.primeStripAt n m).action v g x) =
      (I.primeStripAt (n + 1) m).action v (galoisIso v g) (valueIso v x)

noncomputable def actualLGPPolyIsoValueUnitData
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    LGPPolyIsoValueUnitData I n m where
  valueIso := fun v => (I.primeStripLinkAt n m (n + 1) m).isoMon v
  galoisIso := fun v => (I.primeStripLinkAt n m (n + 1) m).isoPi v
  unitIso := fun v => (I.primeStripLinkAt n m (n + 1) m).isoG v
  degree_compat := fun v x => (I.primeStripLinkAt n m (n + 1) m).compatDegree v x
  proj_compat := fun v => (I.primeStripLinkAt n m (n + 1) m).compatProj v
  action_compat := fun v g x => (I.primeStripLinkAt n m (n + 1) m).compatAction v g x

theorem actualLGPPolyIso_degree_preserved
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) (v : V)
    (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripAt (n + 1) m).degree v
        ((actualLGPPolyIsoValueUnitData I n m).valueIso v x) =
      (I.primeStripAt n m).degree v x :=
  (actualLGPPolyIsoValueUnitData I n m).degree_compat v x

theorem actualLGPPolyIso_action_natural
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) (v : V)
    (g : (I.primeStripAt n m).toDPrimeStrip.Pi v)
    (x : (I.primeStripAt n m).Mon v) :
    (actualLGPPolyIsoValueUnitData I n m).valueIso v
        ((I.primeStripAt n m).action v g x) =
      (I.primeStripAt (n + 1) m).action v
        ((actualLGPPolyIsoValueUnitData I n m).galoisIso v g)
        ((actualLGPPolyIsoValueUnitData I n m).valueIso v x) :=
  (actualLGPPolyIsoValueUnitData I n m).action_compat v g x

end LeanFormal.IUT.XiFPaper.S3137ThetaXMuLGPRelativeActual

namespace LeanFormal.IUT.Audit

/-- **Exact source gap for the Theta x mu LGP-link.**  IUT III, Definition 3.8,
(ii) (pp. 112--113), with IUT II, Definition 4.9, (viii): the LGP-link is a full
poly-isomorphism of F^LGP x mu-prime-strips.  The tree's HodgeTheaterLink supplies
the underlying F-prime-strip equivalence and hence its value-monoid and unit-group
parts (constructed in S3137ThetaXMuLGPRelativeActual), but it does NOT contain the
F^LGP x mu-prime-strip carrier, nor the full poly-isomorphism (a family of
isomorphisms modulo indeterminacy).  Pending; no inhabitant, no milestone. -/
def thetaXMuLGPFullPolyIsomorphism : Obligation :=
  { id := "IUT-III.theta-xmu-LGP-full-poly-isomorphism"
    source := "IUT III, Definition 3.8, (ii), pp. 112-113; IUT II, Definition 4.9, (viii)"
    status := VerificationStatus.pending
    note := "The tree has the F-prime-strip link with its value-monoid and unit-group parts, but not the F^LGP x mu-prime-strip nor the full poly-isomorphism of Definition 3.8, (ii).  Missing carrier; not substituted."
    dependsOn := ["S3137ThetaXMuLGPRelativeActual"] }

end LeanFormal.IUT.Audit