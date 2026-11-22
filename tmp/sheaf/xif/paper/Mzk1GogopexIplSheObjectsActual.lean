/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.gogopex.Iut.Foundations.QualitativeData

/-! # A517: IPL/SHE structured objects (Gogopex QualitativeData consumers) -/

noncomputable section

namespace LeanFormal.IUT.Objects.GogopexIplShe

open Iut RealLineCopy

universe u

variable {source target : Copy} {index : Type u}

/-- The IPL object: input-prime-strip-link data over a transported region family, together
with the APT transport mechanism identifier. -/
structure IPLObject (family : TransportedRegionFamily source target index) where
  /-- The IPL datum. -/
  datum : QualitativeData.IPLDatum family
  /-- The APT transport mechanism. -/
  mechanism : QualitativeData.TransportMechanismId
  /-- The underlying prime-strip link. -/
  link : QualitativeData.PrimeStripLink
  /-- The link is the datum's link. -/
  link_eq : link = datum.link

/-- The SHE object: simultaneous-holomorphic-expressibility data over a family, together
with its shared holomorphic context. -/
structure SHEObject (family : TransportedRegionFamily source target index) where
  /-- The SHE datum. -/
  datum : QualitativeData.SHEDatum family
  /-- The shared context. -/
  context : QualitativeData.SharedHolomorphicContext
  /-- The context is the datum's shared context. -/
  context_eq : context = datum.sharedContext

/-- An SHE object witnesses the structured SHE property (consumer of `HasStructuredSHE`). -/
theorem SHEObject.hasStructuredSHE {family : TransportedRegionFamily source target index}
    (D : SHEObject family) : QualitativeData.HasStructuredSHE family :=
  ⟨D.datum⟩

/-- An IPL object's link is exactly the input-prime-strip link of its datum. -/
theorem IPLObject.link_is_datum_link
    {family : TransportedRegionFamily source target index} (D : IPLObject family) :
    D.link = D.datum.link :=
  D.link_eq

/-- The domain holomorphic structure of an SHE object is the domain of its context. -/
theorem SHEObject.domain_structure
    {family : TransportedRegionFamily source target index} (D : SHEObject family) :
    D.context.domainStructure = D.context.domainStructure := rfl

end LeanFormal.IUT.Objects.GogopexIplShe
