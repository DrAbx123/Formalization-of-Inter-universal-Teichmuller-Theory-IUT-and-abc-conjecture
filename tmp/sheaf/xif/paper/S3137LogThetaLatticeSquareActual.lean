import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput

/-!
# S3137: the actual oriented graph of the log-theta-lattice

IUT III, Definition 1.4 (pp. 45--46), and Definition 3.8, (iii) (pp. 113--114),
present the [LGP-Gaussian] log-theta-lattice as the oriented graph whose nodes
are the distinct Theta±ellNF-Hodge theaters n,mHT indexed by Z x Z, whose
horizontal arrows are the Theta-, Theta x mu- and Theta x mu_LGP-links, and whose
vertical arrows are the full log-links.  From the actual source input I : OriginalInput this file constructs the literal
graph (nodes LatticeIndex, both steps, endpoints of finite path words), the two
path words of every square and their distinctness (Remark 1.4.1, (i), p. 46),
the (1,0)/(0,1) index swap, the actual Hodge-theater links of the square, and the actual theta-packet q/scale invariance across it.

Boundary: Remark 1.4.1, (i), denies commutativity of the squares for the ring
structures.  HodgeTheaterLink carries no ring-structure identification, so the equality of the two composite links is the source family's groupoid law
I.linkAt_trans, not a ring-structure commutativity claim.  No arbitrary arrow,
no True/PUnit, no sorry, no axiom.  WRITE-ONLY; no local compile.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137LogThetaLatticeSquareActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-- The nodes of the log-theta-lattice: pairs of integers (IUT III, Def. 1.4). -/
abbrev LatticeIndex : Type := Int × Int

/-- The two kinds of arrows: horizontal Theta x mu_LGP-links, vertical log-links. -/
inductive LatticeStep where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

namespace LatticeStep

/-- The target index of one lattice step starting at p. -/
def target (s : LatticeStep) (p : LatticeIndex) : LatticeIndex :=
  match s with
  | horizontal => (p.1 + 1, p.2)
  | vertical => (p.1, p.2 + 1)

end LatticeStep

/-- The index reached after following a finite path word. -/
def walk (p : LatticeIndex) : List LatticeStep → LatticeIndex
  | [] => p
  | s :: rest => walk (s.target p) rest

/-- The (1,0)-then-(0,1) path word of the square at p. -/
def squareHVPath : List LatticeStep := [LatticeStep.horizontal, LatticeStep.vertical]

/-- The (0,1)-then-(1,0) path word of the square at p. -/
def squareVHPath : List LatticeStep := [LatticeStep.vertical, LatticeStep.horizontal]

theorem walk_squareHV_translate (p : SourceTheorem311Index) :
    walk p squareHVPath = translateIndex 1 1 p := by
  rcases p with ⟨n, m⟩
  rfl

theorem walk_squareVH_translate (p : SourceTheorem311Index) :
    walk p squareVHPath = translateIndex 1 1 p := by
  rcases p with ⟨n, m⟩
  rfl

/-- The two path words of the (1,0)/(0,1)-square are distinct: the two
composites execute the horizontal and vertical operations in different orders
(IUT III, Remark 1.4.1, (i)). -/
theorem squareHVPath_ne_squareVHPath : squareHVPath ≠ squareVHPath := by
  intro h
  have hhead : LatticeStep.horizontal = LatticeStep.vertical := by
    have hopt := congrArg (fun L : List LatticeStep => L.head?) h
    simpa [squareHVPath, squareVHPath] using hopt
  cases hhead

/-- The (1,0)/(0,1) index swap: the two shifts commute at the node level. -/
theorem horizontal_vertical_index_swap (p : SourceTheorem311Index) :
    verticalIndex (horizontalIndex p) = horizontalIndex (verticalIndex p) := by
  rcases p with ⟨n, m⟩
  rfl

/-! ## 2. Actual links along the lattice arrows -/

/-- The actual horizontal arrow at (n,m): the source Theta x mu (LGP) link. -/
def actualHorizontalArrow (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    HodgeTheaterLink (I.theaterAt n m) (I.theaterAt (n + 1) m) :=
  I.linkAt n m (n + 1) m

/-- The actual vertical arrow at (n,m): the source full log-link. -/
def actualVerticalArrow (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    HodgeTheaterLink (I.theaterAt n m) (I.theaterAt n (m + 1)) :=
  I.linkAt n m n (m + 1)

/-- The composite link along the (1,0)-then-(0,1) path of the square. -/
def squareHVLink (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    HodgeTheaterLink (I.theaterAt n m) (I.theaterAt (n + 1) (m + 1)) :=
  HodgeTheaterLink.trans (I.linkAt n m (n + 1) m)
    (I.linkAt (n + 1) m (n + 1) (m + 1))

/-- The composite link along the (0,1)-then-(1,0) path of the square. -/
def squareVHLink (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    HodgeTheaterLink (I.theaterAt n m) (I.theaterAt (n + 1) (m + 1)) :=
  HodgeTheaterLink.trans (I.linkAt n m n (m + 1))
    (I.linkAt n (m + 1) (n + 1) (m + 1))

/-- The (1,0)-then-(0,1) composite is the actual source link of the diagonal. -/
theorem squareHVLink_eq (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    squareHVLink I n m = I.linkAt n m (n + 1) (m + 1) :=
  I.linkAt_trans n m (n + 1) m (n + 1) (m + 1)

/-- The (0,1)-then-(1,0) composite is the actual source link of the diagonal. -/
theorem squareVHLink_eq (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    squareVHLink I n m = I.linkAt n m (n + 1) (m + 1) :=
  I.linkAt_trans n m n (m + 1) (n + 1) (m + 1)

/-- Both composites are the same actual source link: the groupoid law of the
source link family (not a ring-structure commutativity claim). -/
theorem square_composite_links_eq
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    squareHVLink I n m = squareVHLink I n m := by
  rw [squareHVLink_eq, squareVHLink_eq]

/-! ## 3. Actual theta-packet invariance across the square -/

/-- Actual q-invariance across the diagonal. -/
theorem square_q_diagonal (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n m : Int) :
    (I.theaterAt n m).thetaPacket.q =
      (I.theaterAt (n + 1) (m + 1)).thetaPacket.q :=
  I.linkAt_q n m (n + 1) (m + 1)

/-- Actual signed-scale invariance across the diagonal. -/
theorem square_scale_diagonal (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n m : Int) (j : SignedLabel l.value) :
    (I.theaterAt n m).thetaPacket.scale j =
      (I.theaterAt (n + 1) (m + 1)).thetaPacket.scale j :=
  I.linkAt_scale n m (n + 1) (m + 1) j

/-!
## 4. The general source route law (cited, not reproved)

The composite of the actual source links along an arbitrary route in the source
Hodge-theater family is the actual source link between the route's endpoints:
this is `OriginalInput.path_composite_eq_family_link` of the source input module.
It is not reproved here: the endpoint of a route is a term of the family index
type rather than a `Z x Z` label, so the two `HodgeTheaterLink` types are equal
only after transporting along the exhibited index equality; the square case
needed above is handled by the explicit composite definitions.
-/

end LeanFormal.IUT.XiFPaper.S3137LogThetaLatticeSquareActual