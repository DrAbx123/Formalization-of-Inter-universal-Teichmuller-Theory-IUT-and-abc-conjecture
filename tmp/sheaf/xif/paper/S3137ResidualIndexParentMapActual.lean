import tmp.sheaf.xif.paper.S3137CanonicalResidualIndexActual
import tmp.sheaf.xif.paper.S3137CanonicalResidualIndexPart2Actual
import tmp.sheaf.xif.paper.S3137CanonicalResidualIndexPart3Actual
import tmp.sheaf.xif.paper.S3137CanonicalResidualIndexPart4Actual
import tmp.sheaf.xif.paper.S3137CanonicalResidualIndexPart5Actual
import tmp.sheaf.xif.paper.S3137CanonicalResidualIndexPart6Actual
import tmp.sheaf.xif.paper.S3137CanonicalResidualIndexPart7Actual
import tmp.sheaf.xif.paper.S3137CanonicalResidualIndexPart8Actual
import tmp.sheaf.xif.paper.S3137CanonicalResidualIndexPart9Actual
import tmp.sheaf.xif.paper.S3137CanonicalResidualIndexPart10Actual
import tmp.sheaf.xif.paper.S3137CanonicalResidualIndexPart11Actual
import tmp.sheaf.xif.paper.S3137CanonicalResidualIndexPart12Actual
import tmp.sheaf.xif.paper.S3137CanonicalResidualIndexPart13Actual
import tmp.sheaf.xif.paper.S3137CanonicalResidualIndexPart14Actual

/-!
# S3137 canonical residual index: parent map and totals (task-59)

Alignment map from mainline's 14 registry ids to the `INDEX.*` sub-node ids,
plus totals per part.  Consumers should reference the `INDEX.*` id and keep a
`dependsOn` edge to the parent registry id; no registry id is duplicated. -/

namespace LeanFormal.IUT.Audit

/-- Parent registry id -> ordered sub-node ids `INDEX.*`. -/
def S3137ResidualIndexParentMap : List (String × List String) :=
  [ ("R1.M2M3M5.sameC-q-theta-readout",
      ["INDEX.R1.M2.base-q-transport",
       "INDEX.R1.M2.clause-B-descent",
       "INDEX.R1.M2b.tate-q-identification",
       "INDEX.R1.C3-place-tie"]),
    ("ThetaHalf.vform-canonical-residual",
      ["INDEX.ThetaHalf.vform-canonical-identification",
       "INDEX.ThetaHalf.c3-hull-readout-identification",
       "INDEX.ThetaHalf.final-composition"]),
    ("ThetaHalf.exact-factor-residual",
      ["INDEX.ThetaHalf.normalization-factor-zero",
       "INDEX.ThetaHalf.canonical-rooted-readout"]),
    ("F4.a.value-group-splitting",
      ["INDEX.F4.a.value-monoid-identification"]),
    ("F4.b.paper-scaling-zero",
      ["INDEX.F4.b1.additive-haar-modulus-law",
       "INDEX.F4.b1.haar-uniqueness-scalar-step",
       "INDEX.F4.b1.log-shell-scaling-index",
       "INDEX.F4.b2.integral-log-shell-unit-self-similarity",
       "INDEX.F4.b3.paper-lambda-log-degree-zero"]),
    ("LGP.residuals",
      ["INDEX.LGP.local-tensor-packet-identification",
       "INDEX.LGP.tensor-o-lattice-identification",
       "INDEX.LGP.jv-packet-transport",
       "INDEX.LGP.realified-value-transport",
       "INDEX.LGP.qv-principal-ideal",
       "INDEX.LGP.local-monoid-identification",
       "INDEX.LGP.xmu-unit-portion",
       "INDEX.LGP.frobenioid-mod-to-MOD-iso",
       "INDEX.LGP.frobenioid-carrier-functor",
       "INDEX.LGP.bad-family-packet",
       "INDEX.LGP.bad-weight-normalization",
       "INDEX.LGP.jv-local-generator-transport",
       "INDEX.LGP.global-units-to-local-units",
       "INDEX.LGP.bad-place-units",
       "INDEX.LGP.theta-label-symmetry",
       "INDEX.LGP.local-o-lattice-quasi-lattice",
       "INDEX.LGP.bad-weight-qpilot-comparison"]),
    ("first-triangle.A-C",
      ["INDEX.FT.A.source-log-shell-contract",
       "INDEX.FT.A.source-capsule-data",
       "INDEX.FT.B.source-lgp-data",
       "INDEX.FT.C.fmod-real-algebra",
       "INDEX.FT.C1.infinite-place-choice",
       "INDEX.FT.C2.local-element-map",
       "INDEX.FT.C2.fiber-assignment",
       "INDEX.FT.C.ind1-bridge-dependency",
       "INDEX.FT.C2.coordination",
       "INDEX.FT.C2.conjugate-copy-action",
       "INDEX.FT.C2.reduces-to-M0-M1",
       "INDEX.FT.conditional-theorem",
       "INDEX.FT.public-consumer",
       "INDEX.FT.C2.kummer-copy-action",
       "INDEX.FT.C2.kummer-artin-pairing",
       "INDEX.FT.C2.hom-level-refuted",
       "INDEX.FT.C3.convention-identification",
       "INDEX.FT.final-composition"]) ]

/-- Totals of the canonical sub-node index: 10+15+4+5+2+4+2+4+2+3+2+2+1+1 = 57 entries across 7
parent registry ids. -/
def S3137ResidualIndexTotals : List (String × Nat) :=
  [ ("part1", S3137CanonicalResidualIndexPart1.length),
    ("part2", S3137CanonicalResidualIndexPart2.length),
    ("part3", S3137CanonicalResidualIndexPart3.length),
    ("part4", S3137CanonicalResidualIndexPart4.length),
    ("part5", S3137CanonicalResidualIndexPart5.length),
    ("part6", S3137CanonicalResidualIndexPart6.length),
    ("part7", S3137CanonicalResidualIndexPart7.length),
    ("part8", S3137CanonicalResidualIndexPart8.length),
    ("part9", S3137CanonicalResidualIndexPart9.length),
    ("part10", S3137CanonicalResidualIndexPart10.length),
    ("part11", S3137CanonicalResidualIndexPart11.length),
    ("part12", S3137CanonicalResidualIndexPart12.length),
    ("part13", S3137CanonicalResidualIndexPart13.length),
    ("part14", S3137CanonicalResidualIndexPart14.length),
    ("total", S3137CanonicalResidualIndexPart1.length
      + S3137CanonicalResidualIndexPart2.length
      + S3137CanonicalResidualIndexPart3.length
      + S3137CanonicalResidualIndexPart4.length
      + S3137CanonicalResidualIndexPart5.length
      + S3137CanonicalResidualIndexPart6.length
      + S3137CanonicalResidualIndexPart7.length
      + S3137CanonicalResidualIndexPart8.length
      + S3137CanonicalResidualIndexPart9.length
      + S3137CanonicalResidualIndexPart10.length
      + S3137CanonicalResidualIndexPart11.length
      + S3137CanonicalResidualIndexPart12.length
      + S3137CanonicalResidualIndexPart13.length
      + S3137CanonicalResidualIndexPart14.length) ]

theorem S3137ResidualIndexParentMap_length :
    S3137ResidualIndexParentMap.length = 7 := rfl

theorem S3137ResidualIndex_total_eq :
    S3137ResidualIndexTotals =
      [("part1", 10), ("part2", 15), ("part3", 4), ("part4", 5), ("part5", 2),
        ("part6", 4), ("part7", 2), ("part8", 4), ("part9", 2), ("part10", 3),
        ("part11", 2), ("part12", 2), ("part13", 1), ("part14", 1),
        ("total", 57)] := rfl

end LeanFormal.IUT.Audit