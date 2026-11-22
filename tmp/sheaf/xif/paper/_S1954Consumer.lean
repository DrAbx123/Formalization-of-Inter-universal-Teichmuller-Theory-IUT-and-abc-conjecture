import tmp.sheaf.xif.paper.S1954ArchimedeanPeriodActual

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1950ArchimedeanLogShellActual
open LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual

-- The full, period-carrying archimedean log-shell datum and its construction.
#check @LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.PaperArchimedeanLogShellDatum
#check @LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.paperArchimedeanLogShellDatum
#check @LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.paperArchimedeanLogShellDatum_logShell
#check @LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.paperArchimedeanLogShellDatum_period

-- The three period-carrying features: period generator, fundamental segment, orbit, upper semi.
#check @LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.archimedeanExp_eq_one_iff
#check @LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.mem_paperFundamentalSegment_iff
#check @LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.mem_paperLogShell_iff_unit_mul_segment
#check @LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.archimedeanUnitSphere_subset_exp_paperLogShell
#check @LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.not_exp_paperLogShell_subset

-- The exact boundary relative to S1927/S1950.
#check @LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.no_logShell_subset_unitBall
#check @LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.real_place_not_inhabited
#check @LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.s1950_not_full
#check @LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.s1954_exact_boundary

example (D : S1895PaperInput) (w : NumberField.InfinitePlace (PaperFmod D))
    (hw : w.IsComplex) : Nonempty (PaperArchimedeanLogShellDatum D w) :=
  nonempty_paperArchimedeanLogShellDatum D w hw

example (D : S1895PaperInput) (w : NumberField.InfinitePlace (PaperFmod D))
    (hreal : w.IsReal) : ¬ Nonempty (PaperArchimedeanLogShellDatum D w) :=
  real_place_not_inhabited D w hreal

example (D : S1895PaperInput) (w : NumberField.InfinitePlace (PaperFmod D))
    (hw : w.IsComplex) (F : PaperArchimedeanLogShellDatum D w) :
    ¬ F.logShell ⊆ archimedeanUnitBall D w :=
  no_logShell_subset_unitBall D w hw F

example (D : S1895PaperInput) (w : NumberField.InfinitePlace (PaperFmod D))
    (hw : w.IsComplex) :
    (paperArchimedeanLogShellDatum D w hw).logShell = {x : w.Completion | ‖x‖ ≤ Real.pi} :=
  rfl

#print axioms LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.paperArchimedeanLogShellDatum
#print axioms LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.archimedeanExp_eq_one_iff
#print axioms LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.archimedeanUnitSphere_subset_exp_paperLogShell
#print axioms LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.mem_paperLogShell_iff_unit_mul_segment
#print axioms LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.two_pi_le_norm_period
#print axioms LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.no_logShell_subset_unitBall
#print axioms LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.real_place_not_inhabited
#print axioms LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.s1950_not_full
#print axioms LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual.s1954_exact_boundary

end
