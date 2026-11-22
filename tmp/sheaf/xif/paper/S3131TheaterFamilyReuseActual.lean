import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual

/-! # S3131 theater-family prior art reuse (model route) -/

namespace LeanFormal.IUT.XiFPaper.S3131TheaterFamilyReuseActual

def S3131TheaterFamilyReuse : List (String × String) :=
  [ ("SourceUnitRegionHaarDataActual.lean:122", "sourceHaarActualPrimeStrip -> REUSE"),
    ("SourceUnitRegionHaarDataActual.lean:146", "Theater -> REUSE"),
    ("SourceUnitRegionHaarDataActual.lean:151", "PrimeStripEquiv -> REUSE"),
    ("SourceUnitRegionHaarDataActual.lean:213", "TheaterLink + laws 224-284 -> REUSE"),
    ("SourceUnitRegionHaarDataActual.lean:288", "Theater_injective -> REUSE"),
    ("SourceUnitRegionHaarDataActual.lean:322/346", "Family + OriginalInput construction -> REUSE for model-route M1/theater (no re-proving)") ]

theorem S3131TheaterFamilyReuse_length : S3131TheaterFamilyReuse.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.S3131TheaterFamilyReuseActual