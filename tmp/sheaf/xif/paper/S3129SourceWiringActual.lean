import LeanFormal.IUT.IUTIII.Theorem311.SourceInternalWiring

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge
open LeanFormal.IUT.Theorem311Source.SourceDependencyChain
open LeanFormal.IUT.Audit

universe ua uv upi umon ui u v w ux uy

namespace LeanFormal.IUT.XiFPaper.S3129SourceWiringActual

variable {l : PrimeGeFive}
variable {V : Type uv}
variable {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-- Minimal real part of the internal source wiring: the alignment and K2 boundary
are explicit source-facing data; the K1 boundary and its vertical realization are
actual projections from the supplied realization via `k1OfRealization`/`toSource`. -/
structure SourceWiringMinimal
    (I : OriginalInput.{u, uv, upi, umon, ui} l V)
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice)
    (X : Type ux) (Y : Type uy) [CommMonoid X] [CommMonoid Y] where
  alignment : SourceH1H2Alignment I R
  k1 : K1VerticalBoundary R.procession R.packet
  k1_eq : k1 = k1OfRealization R
  vertical : SourceVerticalRealization R.procession R.packet
  vertical_eq : vertical = k1.toSource
  k2 : K2FrobenioidBoundary R k1 X Y

namespace SourceWiringMinimal

variable {I : OriginalInput.{u, uv, upi, umon, ui} l V}
variable {R : SourceTheorem311Realization.{u, v, w} l Label Choice}
variable {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]

/-- Canonical minimal wiring: K1 is the actual `k1OfRealization R`; its vertical
realization is the actual `K1VerticalBoundary.toSource`; the alignment and the K2
Frobenioid boundary are supplied explicitly, not manufactured. -/
def canonical
    (A : SourceH1H2Alignment I R)
    (B : K2FrobenioidBoundary R (k1OfRealization R) X Y) :
    SourceWiringMinimal I R X Y :=
  { alignment := A
    k1 := k1OfRealization R
    k1_eq := rfl
    vertical := (k1OfRealization R).toSource
    vertical_eq := rfl
    k2 := B }

@[simp] theorem canonical_alignment
    (A : SourceH1H2Alignment I R)
    (B : K2FrobenioidBoundary R (k1OfRealization R) X Y) :
    (canonical A B).alignment = A := rfl

@[simp] theorem canonical_k1
    (A : SourceH1H2Alignment I R)
    (B : K2FrobenioidBoundary R (k1OfRealization R) X Y) :
    (canonical A B).k1 = k1OfRealization R := rfl

@[simp] theorem canonical_vertical
    (A : SourceH1H2Alignment I R)
    (B : K2FrobenioidBoundary R (k1OfRealization R) X Y) :
    (canonical A B).vertical = (k1OfRealization R).toSource := rfl

@[simp] theorem canonical_k1_vertical_toSource
    (A : SourceH1H2Alignment I R)
    (B : K2FrobenioidBoundary R (k1OfRealization R) X Y) :
    (canonical A B).k1.toSource = (canonical A B).vertical := rfl

@[simp] theorem canonical_k2
    (A : SourceH1H2Alignment I R)
    (B : K2FrobenioidBoundary R (k1OfRealization R) X Y) :
    (canonical A B).k2 = B := rfl

end SourceWiringMinimal

/-- Audit record: the minimal wiring uses actual K1 construction; alignment and
K2 remain explicit source-facing fields. -/
def sourceWiringMinimal : Obligation :=
  { id := "IUT-III.source-internal-wiring.minimal"
    source := "IUT III Theorem 3.11 opening; Theorem311/SourceInternalWiring.lean"
    status := VerificationStatus.interface
    note := "Minimal real part: K1 = k1OfRealization R and vertical = K1.toSource are actual projections; SourceH1H2Alignment and K2FrobenioidBoundary are explicit fields, not manufactured."
    dependsOn :=
      [ "IUT-III.source-h1-h2-construction",
        "IUT-III.K1.vertical-log-kummer-boundary",
        "IUT-III.K2.frobenioid-mod-realification-boundary" ] }

#check SourceWiringMinimal.canonical
#check sourceWiringMinimal

end LeanFormal.IUT.XiFPaper.S3129SourceWiringActual
end
