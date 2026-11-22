# T11 actual — completion, obligation closure, exact residual

## Scope

- Node: S3-T11 strict closure.
- Files: tmp/sheaf/n8/closure/T11Actual.lean and this record.
- Modified: tmp/sheaf/n8/closure/SourceThetaToIQ.lean (actual interface
  construction and zero-sorry sourceThetaIQObligation).
- No production file edited; no large build run.
- Target: actual thetaCompletion from C3 qUnit/thetaPacket, thetaScale
  compatibility, C4 value-monoid -> IQ alignment, sourceThetaIQObligation zero
  sorry or exact no-go, no free interface.

## Actual objects

C3 provides:

~~~text
C3.qUnit : (CommonPrimeCompletion (K := Fmod) C3.place)^x
C3.qUnit_eq : qUnit = candidateUnits C3.place C3.q
C3.thetaPacket : FiniteThetaPacket l
C3.thetaPacket.scale : SignedLabel l.value -> Real
C3.thetaPacket.q : Real
C3.thetaPacket.log_scale :
  Real.log (scale j) = (gaussExponent j.1).toNat * Real.log C3.thetaPacket.q
C3.tensorLanding : CommonPrimeCompletion -> ArithmeticTensorTupleBlock
C3.tensorUnit : (ArithmeticTensorTupleBlock)^x
C3.tensorLanding_q : tensorLanding q = tensorUnit
~~~

Source theta scale (T11):

~~~text
thetaScale C3 n j : Real = I.thetaValueAt (n.1 : Int) 0 j
~~~

## Actual construction

T11Actual defines the completion candidate

~~~text
thetaCompletionActual C3 n j :
  CommonPrimeCompletion (K := Fmod) C3.place :=
  ((C3.qUnit : CommonPrimeCompletion) ^ (gaussExponent j.1).toNat)
~~~

This uses C3's actual qUnit and the label's Gaussian exponent. It is not a free
interface field and not an arbitrary Type.

The actual interface is

~~~text
thetaIQInterfaceActual C3 : SourceThetaIQInterface C3 where
  thetaCompletion := thetaCompletionActual C3
  thetaScale := fun n j => thetaScale C3 n j
  thetaScale_eq := rfl
  thetaImage := fun n j => C3.tensorLanding (thetaCompletionActual C3 n j)
  thetaImage_eq := rfl
~~~

and consequently

~~~text
sourceThetaIQObligation_actual C3 :
  SourceThetaIQObligation C3 :=
  <thetaIQInterfaceActual C3>
~~~

The corresponding declaration in SourceThetaToIQ.lean was also replaced: its
sourceThetaIQObligation now has the same actual proof, not sorry. The only
remaining completion interface is inhabited; it is no longer a free interface.

## thetaScale compatibility: what is proved and what is not

Proved:

~~~text
thetaScaleActual_eq_source :
  thetaScaleActual C3 n j = I.thetaValueAt (n.1 : Int) 0 j
~~~

and, conditional on the source/packet identification,

~~~text
thetaScale_log_eq_gauss_of_packet
  (h : ThetaScalePacketIdentification C3) :
  Real.log (thetaScale C3 n j) =
    (gaussExponent j.1).toNat * Real.log C3.thetaPacket.q
~~~

where

~~~text
ThetaScalePacketIdentification C3 : Prop :=
  forall n j, thetaScale C3 n j = C3.thetaPacket.scale j
~~~

NOT proved: ThetaScalePacketIdentification itself. The source theta value is
read from I.thetaValueAt / theaterAt thetaPacket; C3.thetaPacket is a separate
C3 field, and no production theorem links them. This is the exact missing source
link. It is a Prop obligation, not a free data field.

## Exact no-go for the qUnit candidate as an n-dependent source map

The qUnit candidate is independent of the procession n:

~~~text
thetaCompletionActual_n_independent C3 n n' j :
  thetaCompletionActual C3 n j = thetaCompletionActual C3 n' j
~~~

Thus the actual qUnit construction cannot by itself be the n-dependent source
theta map: it carries no n and no Real theta value. It is an actual completion
candidate, but not a proved image of the source real theta special value.

This is the precise obstruction: a map

~~~text
Real theta value -> CommonPrimeCompletion
~~~

would require either
- a source theorem identifying thetaScale with a completion element, or
- a source embedding/q-comparison Real -> Completion.

Neither exists. The qUnit candidate factors only the label exponent and C3.qUnit.

No formal no-go theorem about all possible maps is proved; the n-independence
theorem is a formal no-go for treating this actual candidate as the source
n-dependent map. The exact missing donor remains:

~~~text
ThetaScalePacketIdentification C3
  (equivalently a source map thetaScale -> completion compatible with C3.qUnit)
~~~

## C4 value-monoid -> IQ alignment

T11Actual restates the C4 alignment:

~~~text
DegreeFaithful C4 :=
  forall b, I.logDegreeAt 0 0 C4.place.v
    (C4.place.R.posRealAction (Multiplicative.ofAdd b)) = b

c4_logDegree_eq_log_thetaScale C4 C3 hdeg n j :
  I.logDegreeAt 0 0 C4.place.v (I.thetaImageValue C4.place.R n j)
    = Real.log (thetaScale C3 n j)
~~~

Proof: thetaImageValue_eq_ofAdd_gauss, DegreeFaithful, and
log_thetaValueAt_eq_gauss. This is the actual common invariant.

A full map from the C4 value monoid to IQCarrier remains an explicit obligation:

~~~text
structure ValueMonoidToIQMap C4 C3 D where
  toIQ : I.ValueMonoidAt 0 0 C4.place.v -> IQCarrier C3
  thetaImage_compat : forall n j,
    toIQ (I.thetaImageValue C4.place.R n j) = D.thetaImage n j

ValueMonoidToIQObligation C4 C3 D := Nonempty (ValueMonoidToIQMap C4 C3 D)
~~~

No inhabitant is constructed. No arbitrary function is introduced. C4 remains
an independent source witness; no C4 IQ proxy is created.

## Status

- T11Actual.lean single-file compile: exit 0.
- SourceThetaToIQ.lean single-file compile: exit 0, sourceThetaIQObligation
  zero sorry (actual thetaIQInterfaceOfQUnit proof).
- No large build.
- Actual thetaCompletion: constructed from C3.qUnit/thetaPacket exponent.
- sourceThetaIQObligation: zero sorry.
- thetaScale compatibility: definitional to I.thetaValueAt; exact missing source
  link ThetaScalePacketIdentification.
- C4 alignment: log-degree theorem proved under DegreeFaithful; full value map
  remains exact obligation.
- Formal no-go: qUnit candidate is n-independent; no universal no-go theorem.
- Production edits: none.

## Next exact action

Prove or refute ThetaScalePacketIdentification C3 from the source theta packet
and C3 construction. If it is false, supply the concrete counterexample
(C3.thetaPacket field differing from the source theater packet); if true, add
the actual source theorem linking I.thetaValueAt (n.1) 0 j to
C3.thetaPacket.scale j. Until then, the qUnit completion is an actual candidate
but not a source-realized theta completion, and the full C4 value-to-IQ map
remains ValueMonoidToIQObligation.
