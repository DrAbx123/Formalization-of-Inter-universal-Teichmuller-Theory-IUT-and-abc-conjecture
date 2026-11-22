import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: the actual BPS (basic prime-strip, F-turnstile-times-mu-prime-strip)

Stage-1 named object: the BPS of IUT III, Theorem 3.11 / Corollary 3.12, the
"basic prime-strip" of the Θ-link gluing data.  Source: Formalization of IUT
(2026-04), §4 :443-513 (BPS def. :462-464, "F ⊩▶ × μ-prime-strip"; first two
triangles :472-513, BPS glued by a full poly-isomorphism to the underlying BPS
of the Θ-pilot at (0,0)), and IUT III, Theorem 3.11(i) / Remark 3.11.1(iii).

This file is *not* an empty shell: the carrier is the existing actual
`SourceFTimesMuPrimeStrip` (`Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism
.lean`), whose underlying F-prime-strip, times-mu fibers, quotient link,
descended action and realified degree are all actual structures.  The Θ-link
gluing data is the actual full poly-isomorphism carrier
`SourceFTimesMuPrimeStripEquivalence`; for the Θ-link endpoints of an actual
`OriginalInput` it is built from the actual `HodgeTheaterLink.primeStripEquiv`
through the proved canonical lifting `canonicalLift`.

The named hypothesis `SourceBPSThetaPilotGluing` records the paper's gluing of
the algorithm input BPS to the underlying BPS of the Θ-pilot at (0,0); it is
exactly the existence of an actual times-mu equivalence, and it is shown
nonempty for the canonical BPS (no arbitrary proposition is introduced).
-/

namespace LeanFormal.IUT.XiFPaper.S3139SourceBPSActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe uv umon upi ua ui

variable {V : Type uv}
variable {l : PrimeGeFive}

/-! ## 1. The BPS carrier -/

/-- The actual BPS carrier: an `F ⊩▶ × μ`-prime-strip, i.e. an F-prime-strip
together with its times-mu layer and the proved quotient/action/degree laws
(the existing actual carrier `SourceFTimesMuPrimeStrip`). -/
structure SourceBPS (V : Type uv) where
  /-- the actual F-turnstile-times-mu-prime-strip -/
  timesMuStrip : SourceFTimesMuPrimeStrip.{uv, umon, upi} V

namespace SourceBPS

/-- The underlying F-prime-strip of a BPS. -/
def underlying (B : SourceBPS V) : FPrimeStrip.{umon, uv, upi} V :=
  B.timesMuStrip.toFPrimeStrip

/-- The etale-like portion `G_v` of the BPS (Formalization :459-460): the
mono-analytic group fibers of the underlying F-prime-strip. -/
def etaleLikePortion (B : SourceBPS V) (v : V) : Type upi :=
  B.underlying.toDPrimeStrip.G v

/-- The etale-like portion carries its actual group structure. -/
instance etaleLikePortionGroup (B : SourceBPS V) (v : V) :
    Group (B.etaleLikePortion v) :=
  B.underlying.toDPrimeStrip.groupG v

end SourceBPS

/-! ## 2. Canonical BPS of an actual prime strip / Hodge theater -/

/-- The actual BPS of a prime strip: the canonical times-mu strip of the
actual F-prime-strip (torsion quotient of the unit groups). -/
def sourceBPSOfStrip (F : FPrimeStrip.{umon, uv, upi} V) : SourceBPS V where
  timesMuStrip := SourceFTimesMuPrimeStrip.canonical F

@[simp] theorem sourceBPSOfStrip_underlying
    (F : FPrimeStrip.{umon, uv, upi} V) :
    (sourceBPSOfStrip F).underlying = F := rfl

/-- The actual BPS of the Hodge theater at the lattice point `(n,m)`. -/
def sourceBPSOfTheater (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n m : Int) : SourceBPS V :=
  sourceBPSOfStrip (I.theaterAt n m).primeStrip

@[simp] theorem sourceBPSOfTheater_underlying
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    (sourceBPSOfTheater I n m).underlying = (I.theaterAt n m).primeStrip := rfl

/-! ## 3. The Θ-link gluing data -/

/-- The Θ-link gluing data between two BPS: a full poly-isomorphism, carried
by the actual times-mu prime-strip equivalence (Formalization :507-513). -/
structure SourceBPSThetaGluing (S T : SourceBPS V) where
  /-- the actual full poly-isomorphism between the two times-mu strips -/
  glue : SourceFTimesMuPrimeStripEquivalence S.timesMuStrip T.timesMuStrip

namespace SourceBPSThetaGluing

variable {S T U : SourceBPS V}

/-- Composite gluing. -/
def trans (G : SourceBPSThetaGluing S T) (H : SourceBPSThetaGluing T U) :
    SourceBPSThetaGluing S U :=
  ⟨SourceFTimesMuPrimeStripEquivalence.trans G.glue H.glue⟩

/-- The etale-like portion transported by the gluing: the actual group
isomorphism `G_v(S) ~ G_v(T)`. -/
def etaleLikeEquiv (G : SourceBPSThetaGluing S T) (v : V) :
    S.etaleLikePortion v ≃* T.etaleLikePortion v :=
  G.glue.toF.isoG v

/-- The degree readout is preserved by the gluing. -/
theorem degree_eq (G : SourceBPSThetaGluing S T) (v : V)
    (x : S.timesMuStrip.timesMu v) :
    T.timesMuStrip.timesMuDegree v (G.glue.isoTimesMu v x) =
      S.timesMuStrip.timesMuDegree v x :=
  G.glue.compatDegree v x

end SourceBPSThetaGluing

/-! ## 4. Θ-link gluing of actual theaters -/

/-- The Θ-link gluing induced by an actual Hodge-theater link: the canonical
lifting of the actual prime-strip equivalence is the actual full
poly-isomorphism of the BPS endpoints. -/
def sourceBPSThetaGluingOfStripEquiv
    {F F' : FPrimeStrip.{umon, uv, upi} V} (φ : FPrimeStripEquiv F F') :
    SourceBPSThetaGluing (sourceBPSOfStrip F) (sourceBPSOfStrip F') :=
  ⟨SourceFTimesMuPrimeStripEquivalence.canonicalLift φ⟩

/-- The underlying prime-strip equivalence of the gluing is the given one. -/
theorem sourceBPSThetaGluingOfStripEquiv_toF
    {F F' : FPrimeStrip.{umon, uv, upi} V} (φ : FPrimeStripEquiv F F') :
    (sourceBPSThetaGluingOfStripEquiv φ).glue.toF = φ := rfl

/-- The Θ-link gluing data of two actual Hodge theaters. -/
def sourceBPSThetaGluingOfLink
    {A B : HodgeTheater.{ua, uv, upi, umon} l V}
    (L : HodgeTheaterLink A B) :
    SourceBPSThetaGluing (sourceBPSOfStrip A.primeStrip)
      (sourceBPSOfStrip B.primeStrip) :=
  sourceBPSThetaGluingOfStripEquiv L.primeStripEquiv

/-- The Θ-link gluing data between the BPS of the theaters at `(n,m)` and
`(n',m')` of an actual original input. -/
def sourceBPSThetaGluingAt (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n m n' m' : Int) :
    SourceBPSThetaGluing (sourceBPSOfTheater I n m)
      (sourceBPSOfTheater I n' m') :=
  sourceBPSThetaGluingOfLink (I.linkAt n m n' m')

/-- The underlying strip equivalence of the Θ-link gluing at the actual
lattice points is the actual link's prime-strip equivalence. -/
theorem sourceBPSThetaGluingAt_toF
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m n' m' : Int) :
    (sourceBPSThetaGluingAt I n m n' m').glue.toF =
      (I.linkAt n m n' m').primeStripEquiv := rfl

/-- The Θ-link endpoints carry the same actual Theta q (vertical coricity of
the theta-packet data underlying the gluing). -/
theorem sourceBPSThetaGluingAt_q
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m n' m' : Int) :
    (I.theaterAt n m).thetaPacket.q = (I.theaterAt n' m').thetaPacket.q :=
  (I.linkAt n m n' m').theta_q_eq

theorem sourceBPSThetaGluingAt_scale
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m n' m' : Int)
    (j : SignedLabel l.value) :
    (I.theaterAt n m).thetaPacket.scale j =
      (I.theaterAt n' m').thetaPacket.scale j :=
  (I.linkAt n m n' m').theta_scale_eq j

/-! ## 5. The named Θ-pilot gluing hypothesis (paper, Formalization :507-513) -/

/-- Named hypothesis of the paper: the algorithm-input BPS is glued, via a
full poly-isomorphism, to the underlying BPS of the Θ-pilot at `(0,0)` arising
from the 0-column of the log-theta-lattice (Formalization :507-513).  This is
a concrete existence statement about actual times-mu equivalences, not an
arbitrary proposition. -/
def SourceBPSThetaPilotGluing
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (B : SourceBPS V) : Prop :=
  Nonempty (SourceFTimesMuPrimeStripEquivalence B.timesMuStrip
    (sourceBPSOfTheater I 0 0).timesMuStrip)

/-- The canonical BPS at `(0,0)` satisfies the Θ-pilot gluing hypothesis
(reflexivity of the full poly-isomorphism). -/
theorem sourceBPSThetaPilotGluing_refl
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    SourceBPSThetaPilotGluing I (sourceBPSOfTheater I 0 0) :=
  ⟨SourceFTimesMuPrimeStripEquivalence.refl _⟩

end LeanFormal.IUT.XiFPaper.S3139SourceBPSActual

end
