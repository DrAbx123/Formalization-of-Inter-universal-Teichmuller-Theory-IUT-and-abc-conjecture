/-! # A716 LANA dependency hierarchy audit (ported Iut tree)

Read-only table for hull progress comparison.  Paths under `tmp/external/ported/lana/`
are the gate-counted ported tree; the Tempered entry is a non-counted external
prerequisite leaf.  Derived by reading source `import` lines (no compilation). -/

structure LanaDepRow where
  path : String
  role : String
  imports : String
  deriving Repr

def lanaDepRows : List LanaDepRow :=
  [ { path := "tmp/external/ported/lana/Iut/Cor312/ThetaData/Basic.lean", role := "leaf: theta data", imports := "(base theta-data layer)" },
    { path := "tmp/external/ported/lana/Iut/Cor312/LeftHandSide.lean", role := "Cor312 LHS", imports := "ThetaData.Basic" },
    { path := "tmp/external/ported/lana/Iut/Cor312/ContainerHull.lean", role := "Cor312 container hull", imports := "container layer" },
    { path := "tmp/external/ported/lana/Iut/Cor312/LogVolume.lean", role := "Cor312 log-volume", imports := "log-volume layer" },
    { path := "tmp/external/ported/lana/Iut/Cor312/RightHandSide.lean", role := "Cor312 RHS", imports := "ThetaData.Basic + ContainerHull + LogVolume" },
    { path := "tmp/external/ported/lana/Iut/Cor312/Statement.lean", role := "Cor312 statement", imports := "LeftHandSide + RightHandSide" },
    { path := "tmp/external/ported/lana/Iut/Implication/Invariants.lean", role := "implication invariants", imports := "Cor312.Statement" },
    { path := "tmp/external/ported/lana/Iut/Implication/LogVolumeBound.lean", role := "TARGET: rhs_le", imports := "Implication.Invariants" },
    { path := "tmp/external/ported/lana/Iut/Implication/Theorem110.lean", role := "Theorem 1.10", imports := "Implication.LogVolumeBound" },
    { path := "tmp/external/ported/lana/Iut/Concrete/ThetaRegion.lean", role := "concrete theta region", imports := "ThetaLocalConstruct.Data + Cor312.Statement" },
    { path := "tmp/external/ported/lana/Iut/Concrete/Invariants.lean", role := "concrete invariants", imports := "Concrete.ThetaRegion + Implication.Theorem110" },
    { path := "tmp/external/ported/lana/Iut/Concrete/SectionAverage.lean", role := "section average", imports := "Concrete.Invariants + GaloisPlaces + TorsionFieldGalois" },
    { path := "tmp/external/ported/lana/Iut/Concrete/LocalEstimate.lean", role := "TARGET: local estimates", imports := "Concrete.SectionAverage" },
    { path := "tmp/sheaf/lana/tempered-fundamental-groups", role := "external prerequisite (NOT gate-counted)", imports := "Tempered 25 modules (for Tower/Concrete leaves)" } ]

theorem lanaDepRows_length : lanaDepRows.length = 14 := rfl

/-- The counted set is the ported-lana rows (the Tempered note is external). -/
def lanaDepCountedRows : List LanaDepRow :=
  lanaDepRows.take 13

theorem lanaDepCountedRows_length : lanaDepCountedRows.length = 13 := rfl
