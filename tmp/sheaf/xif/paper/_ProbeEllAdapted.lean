import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveAnabelioid
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
example : (curveY2EqX3SubX.map (algebraMap ℚ GaussianField)).IsElliptic := inferInstance
example : (curveY2EqX3SubX.baseChange GaussianField).IsElliptic := inferInstance
