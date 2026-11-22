import tmp.sheaf.xif.paper.Mzk1GeomCoreFoundationActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Mzk1GeomCoreRRWitnessActual — SUPPLEMENTARY (canonical layer = Mzk1GeomCoreFoundationActual)

Lead A412/A414 consolidation: the standalone RR-witness implementation was merged into
the single canonical foundation file `Mzk1GeomCoreFoundationActual` (RR-independent base
layer + RR-conditional zero_divisor_exists + vacuity-fixed scheme witness + consumer
chain).  This file is kept as a thin SUPPLEMENTARY compatibility view: it re-exports the
canonical declarations and records the merge.  It adds no mathematics and no closure.
Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRWitnessActual

universe u

/-! ## Supplementary re-exports of the canonical foundation -/

export LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual
  (ell_drop_of_rr exists_mem_notMem_of_proper PencilData exists_simple_pole_function
   exists_function_with_zero_divisor GeometricCoreZeroDatum exists_geometricCore_zeroDatum
   zeroSet_eq_T zero_divisor_eq_one zero_divisor_eq_zero zero_divisor_degree
   punctureDivisor degree_punctureDivisor MapsTToZeroOn mapsTToZeroOn_iff zero_divisor_exists)

export LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual.SchemeLayer
  (FibreOverZeroEq fibreOverZeroEq_mapsTToZero fibreOverZeroEq_of_eq_zeroLocus
   Mzk1GeometricCoreWitnessPreciseRestated restatedToPrecise restatedToOld
   recast_of_restated restatedWitness_of_data Mzk1GeometricCoreRecastPreciseRestated
   recast_of_recastRestated genEll15GeometricCoreStatementPrecise_of_restated
   genEll15GeometricCoreStatement_of_restated)

export LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual.Rows (problemDRows problemDRows_length)

/-- Supplemental ledger: this file is a view of the canonical foundation. -/
def rrWitnessRows : List (String × String × String) :=
  [ ("standalone RR-witness implementation", "MERGED", "canonical = tmp/sheaf/xif/paper/Mzk1GeomCoreFoundationActual.lean (EXIT0 results:209293; checker CITABLE 15; probe 209336)")
  , ("RR-conditional function-field layer", "NOT-YET (view)", "zero_divisor_exists re-exported from canonical; named inputs hRR + hdual explicit there")
  , ("scheme witness + consumer chain", "CANONICAL (view)", "FibreOverZeroEq / restated witness / GenEll15 links re-exported from canonical SchemeLayer") ]

theorem rrWitnessRows_length : rrWitnessRows.length = 3 := rfl

#check ell_drop_of_rr
#check punctureDivisor
#check zero_divisor_exists
#check FibreOverZeroEq
#check genEll15GeometricCoreStatement_of_restated
#check rrWitnessRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRWitnessActual
end