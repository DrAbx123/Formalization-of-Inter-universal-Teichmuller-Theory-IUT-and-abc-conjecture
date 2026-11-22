import LeanFormal.IUT.Audit.Status

namespace LeanFormal.IUT.Audit

/-- (i) Packaging constructor: record-to-theater packaging, implemented in
    `HodgeTheater/SourceTheaterRealization.lean`.  The prime-strip carrier
    and the finite theta packet are explicit inputs of the realization, not
    functions of the record. -/
def hodgeTheaterSource : Obligation :=
  { id := "IUT-I.hodge-theater-source"
    source := "IUT I, Section 4"
    status := VerificationStatus.interface
    note := "(i) Packaging constructor implemented in SourceTheaterRealization.lean: structure SourceTheaterRealization (carrier and finite theta packet as explicit inputs), packaged theater with simp projections, SourceTheaterLink algebra (refl/symm/trans with laws), and the toTheaterLink functor onto HodgeTheaterLink; certified at interface level (see Audit.sourceTheaterRealizationPackaging). The source existence problem is split off as IUT-I.hodge-theater-source-existence."
    dependsOn :=
      [ "IUT-I-II.prime-strip-core",
        "IUT-I-II.local-prime-place-carrier",
        "IUT-I.initial-theta-data" ] }

/-- (ii) Source existence: constructing a realization from arbitrary
    Definition 3.1 data alone; still missing (three routes blocked). -/
def hodgeTheaterSourceExistence : Obligation :=
  { id := "IUT-I.hodge-theater-source-existence"
    source := "IUT I, Section 4"
    status := VerificationStatus.pending
    note := "(ii) Source existence: construction of a SourceTheaterRealization from arbitrary Definition 3.1 data alone is not provided; the source construction must supply the arithmetic and geometric structures explicitly. Three routes blocked. R1: carrier extraction from record fields is excluded at theorem level by carrierNotDeterminedByRecord (over the same record and packet there are ZMod 2 and ZMod 4 carrier realizations, and no type is in bijection with both carriers). R2: componentwise local construction has the LocalQParameter/FinitePlaceQCandidate components at arbitrary number-field places, but no packaged FPrimeStrip over arbitrary D.V carrying actions and degrees. R3: the finite model finiteLocalFPrimeStrip 2 7 has index FinitePrimePlace 2 7, not D.V, with no identification map."
    dependsOn :=
      [ "IUT-I-II.prime-strip-core",
        "IUT-I-II.local-prime-place-carrier",
        "IUT-I.initial-theta-data" ] }

end LeanFormal.IUT.Audit
