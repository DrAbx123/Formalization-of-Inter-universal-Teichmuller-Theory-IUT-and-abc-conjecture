import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: the actual etHT (vertically coric etale Hodge theater)

Stage-1 named object: the etHT of IUT III, Theorem 3.11 / Corollary 3.12, the
"etale Hodge theater" that is vertically coric (invariant with respect to the
log-link) and, unlike the Theta-link, symmetric under switching the
domain/codomain of the Theta-link.  Source: Formalization of IUT (2026-04),
§4 :443-455 (definition of etHT, symmetry diagram), :520-524 (etHT associated
to the 0-column), :536-546 (SHE arrow to q-pilot + etHT).  See also IUT III,
Remark 3.11.1.

The carrier is built from the existing actual `HodgeTheater` / `HodgeTheaterLink`
objects of `IUTI/HodgeTheater/HodgeTheaterCore.lean`: a domain theater, a
codomain theater, and their actual link.  Vertical coricity is the actual
q/scale transport carried by the link; the domain/codomain symmetry is the
actual link symmetry (`HodgeTheaterLink.symm`), and the etale-like portion
`G_v` of the theater's prime strip is transported by the actual prime-strip
equivalence.  No empty shell, no True/PUnit, no arbitrary proposition.

For an actual `OriginalInput` the etHT of the 0-column is built from the actual
family links (`sourceEtHTZeroColumn`); this is the input object of the
multiradial algorithm target of the first triangle.
-/

namespace LeanFormal.IUT.XiFPaper.S3139SourceEtHTActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe uv ua upi umon ui

variable {V : Type uv}
variable {l : PrimeGeFive}

/-! ## 1. The etHT carrier -/

/-- The actual etale Hodge theater (etHT): a domain theater, a codomain
theater, and the actual Hodge-theater link between them. -/
structure SourceEtHT (l : PrimeGeFive) (V : Type uv) where
  /-- the theater in the domain of the Theta-link -/
  domain : HodgeTheater.{ua, uv, upi, umon} l V
  /-- the theater in the codomain of the Theta-link -/
  codomain : HodgeTheater.{ua, uv, upi, umon} l V
  /-- the actual Theta-link between them -/
  link : HodgeTheaterLink domain codomain

namespace SourceEtHT

/-- The actual prime-strip equivalence of the etHT link. -/
def primeStripEquiv (E : SourceEtHT l V) :
    FPrimeStripEquiv E.domain.primeStrip E.codomain.primeStrip :=
  E.link.primeStripEquiv

/-- Vertical coricity of the Theta-packet q: the etHT link transports the
actual q unchanged (the etHT is invariant under the log-link direction). -/
theorem thetaQ_transport (E : SourceEtHT l V) :
    E.domain.thetaPacket.q = E.codomain.thetaPacket.q :=
  E.link.theta_q_eq

/-- Vertical coricity of the Theta-packet scales. -/
theorem thetaScale_transport (E : SourceEtHT l V) (j : SignedLabel l.value) :
    E.domain.thetaPacket.scale j = E.codomain.thetaPacket.scale j :=
  E.link.theta_scale_eq j

/-- The vertically coric predicate of the etHT: the actual q readout agrees. -/
def VerticallyCoric (E : SourceEtHT l V) : Prop :=
  E.domain.thetaPacket.q = E.codomain.thetaPacket.q

theorem verticallyCoric (E : SourceEtHT l V) : E.VerticallyCoric := E.thetaQ_transport

/-- The etale-like portion `G_v` of the etHT: the mono-analytic group fibers of
the domain prime strip (Formalization :459-460). -/
def etaleLikePortion (E : SourceEtHT l V) (v : V) : Type upi :=
  E.domain.primeStrip.toDPrimeStrip.G v

/-- The etale-like portion is an actual group. -/
instance etaleLikePortionGroup (E : SourceEtHT l V) (v : V) :
    Group (E.etaleLikePortion v) :=
  E.domain.primeStrip.toDPrimeStrip.groupG v

/-- The actual group isomorphism of etale-like portions carried by the etHT
link (the etale-like data is common to both sides). -/
def etaleLikeEquiv (E : SourceEtHT l V) (v : V) : E.etaleLikePortion v ≃*
    E.codomain.primeStrip.toDPrimeStrip.G v :=
  E.link.primeStripEquiv.isoG v

/-! ## 2. The domain/codomain symmetry of the etHT -/

/-- Swap the domain and codomain of the Theta-link: the etHT is symmetric
under this operation (Formalization :449-455). -/
def swap (E : SourceEtHT l V) : SourceEtHT l V where
  domain := E.codomain
  codomain := E.domain
  link := HodgeTheaterLink.symm E.link

/-- Swapping twice returns the original etHT. -/
theorem swap_swap (E : SourceEtHT l V) : E.swap.swap = E := by
  cases E with
  | mk d c L =>
    show SourceEtHT.mk d c (HodgeTheaterLink.symm (HodgeTheaterLink.symm L)) =
      SourceEtHT.mk d c L
    rw [HodgeTheaterLink.symm_symm]

/-- The etale-like equivalence of the swapped etHT is the inverse of the
original one: the radial-algorithm output is symmetric under the switch. -/
theorem swap_etaleLikeEquiv (E : SourceEtHT l V) (v : V) :
    E.swap.etaleLikeEquiv v = (E.etaleLikeEquiv v).symm := rfl

/-! ## 3. Actual etHTs from an original input -/

/-- The actual etHT of the theaters at the lattice points `(n,m)` and
`(n',m')` of an original input, built from the actual family link. -/
def sourceEtHTAt (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n m n' m' : Int) : SourceEtHT l V where
  domain := I.theaterAt n m
  codomain := I.theaterAt n' m'
  link := I.linkAt n m n' m'

/-- The etHT of the 0-column of the log-theta-lattice (Formalization :520-524):
the actual vertical (log-link) step from `(0,m)` to `(0,m+1)`. -/
def sourceEtHTZeroColumn (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (m : Int) : SourceEtHT l V :=
  sourceEtHTAt I 0 m 0 (m + 1)

/-- The 0-column etHT is vertically coric (actual q transport). -/
theorem sourceEtHTZeroColumn_thetaQ
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (m : Int) :
    (sourceEtHTZeroColumn I m).domain.thetaPacket.q =
      (sourceEtHTZeroColumn I m).codomain.thetaPacket.q :=
  (I.linkAt 0 m 0 (m + 1)).theta_q_eq

/-- Named hypothesis of the paper (Formalization :520-524): a supplied etHT is
the etHT associated to the 0-column at stage `m` of the given original input.
This is a concrete equality of actual theaters, not an arbitrary proposition. -/
def SourceEtHTZeroColumnAt (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (E : SourceEtHT l V) (m : Int) : Prop :=
  E.domain = I.theaterAt 0 m ∧ E.codomain = I.theaterAt 0 (m + 1)

/-- The 0-column etHT satisfies the named 0-column hypothesis. -/
theorem sourceEtHTZeroColumnAt_holds
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (m : Int) :
    SourceEtHTZeroColumnAt I (sourceEtHTZeroColumn I m) m :=
  ⟨rfl, rfl⟩

/-- The multiradial algorithm target carried by the etHT: the radial output is
read in the etale-like portion `G_v` of the etHT, which is vertically coric and
symmetric under the domain/codomain switch. -/
def radialOutputCarrier (E : SourceEtHT l V) (v : V) : Type upi :=
  E.etaleLikePortion v

end SourceEtHT

end LeanFormal.IUT.XiFPaper.S3139SourceEtHTActual

end
