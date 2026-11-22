import tmp.sheaf.xif.paper.S1969ComplexArchimedeanUQActual
import tmp.sheaf.xif.paper.S1958FullLogKummerUQActual
import tmp.sheaf.xif.paper.S1954ArchimedeanPeriodActual

/-!
# S1969 consumer: re-import the built olean and check the interface

Scratch module: imports the compiled S1969 olean, checks the complex-place
archimedean interface, the period-carrying full log-Kummer package, and the
definitional attachment to S1958 and S1954.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1969ComplexArchimedeanUQActual

open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1950ArchimedeanLogShellActual
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual
open LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual
open LeanFormal.IUT.XiFPaper.S1958FullLogKummerUQActual

#check @S1927FirstMissingComplex
#check @paperArchimedeanLogShellComplex
#check @s1927FirstMissingComplex_inhabited
#check @fullFamily_nonempty_iff_allComplex
#check @not_nonempty_fullFamily_of_isReal
#check @not_nonempty_paperDatum_of_isReal
#check @not_reducedDatum_of_fullLogShell
#check @S1969FullLogKummerUQPeriod
#check @paperFullLogKummerUQPeriodOfSquare
#check @paperFullLogKummerUQPeriod
#check @paperFullLogKummerUQPeriod_package
#check @paperFullLogKummerUQPeriod_archimedeanLogShell
#check @paperFullLogKummerUQPeriod_reduced_archimedeanLogShell
#check @paperFullLogKummerUQPeriod_evaluationSquare
#check @s1969_square_corners
#check @paperFullLogKummerUQPeriod_period_norm
#check @s1969FullLogKummerUQPeriod_inhabited
#check @s1969FullLogKummerUQPeriod_nonempty_iff_square
#check @s1969_no_real_place_datum

example (D : S1895PaperInput) : Nonempty (S1927FirstMissingComplex D) :=
  s1927FirstMissingComplex_inhabited D

example (D : S1895PaperInput) (w : NumberField.InfinitePlace (PaperFmod D))
    (hw : w.IsComplex) :
    ((paperFullLogKummerUQPeriod D).archimedeanLogShell w hw).logShell =
      paperLogShell D w :=
  paperFullLogKummerUQPeriod_logShell D w hw

example (D : S1895PaperInput) :
    (paperFullLogKummerUQPeriod D).package = paperFullLogKummerUQ D :=
  paperFullLogKummerUQPeriod_package D

example (D : S1895PaperInput) :
    Nonempty (S1969FullLogKummerUQPeriod D) ↔
      Nonempty (S1927KummerEvaluationSquareActual D) :=
  s1969FullLogKummerUQPeriod_nonempty_iff_square D

example (D : S1895PaperInput) (w : NumberField.InfinitePlace (PaperFmod D))
    (hreal : w.IsReal) :
    ¬ Nonempty (PaperArchimedeanLogShellDatum D w) :=
  not_nonempty_paperDatum_of_isReal D hreal

end LeanFormal.IUT.XiFPaper.S1969ComplexArchimedeanUQActual
