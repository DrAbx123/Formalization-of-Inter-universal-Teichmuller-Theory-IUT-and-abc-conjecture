import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import tmp.sheaf.xif.paper.S1667AdmissibleCurveActual
import Mathlib.Tactic
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual

#check IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
#check concreteFivePadicEquiv
#check concreteFivePadicEquiv.commutes

example : Algebra ℚ concreteFiveCompletion :=
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (NumberField.RingOfIntegers ℚ) ℚ concreteFiveHeightOne
