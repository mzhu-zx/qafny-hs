include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power.dfy"

// target Dafny version: 4.6.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2
import opened Power
import opened DivMod

method GHZ (q_seq'nat'_0__emit : seq<nat>)
  returns ( loc__loc__receiver_3_seq'unsupported'_25__emit : seq<real>
          , q_seq'seq'nat''_24__emit : seq<seq<nat>>
          , q_seq'nat'_26__emit : seq<nat> )
  requires |q_seq'nat'_0__emit| == 15
  requires (forall i : nat | 0 <= i < 15 :: q_seq'nat'_0__emit[i] == 0)
  ensures |loc__loc__receiver_3_seq'unsupported'_25__emit| == 2
  ensures |q_seq'seq'nat''_24__emit| == 2
  ensures (forall j : nat | 0 <= j < 2 :: |q_seq'seq'nat''_24__emit[j]| == 10)
  ensures (forall j : nat | 0 <= j < 2 ::
    (forall k : nat | 0 <= k < 10 :: q_seq'seq'nat''_24__emit[j][k] == j))
  ensures |q_seq'nat'_26__emit| == 5
  ensures (forall i : nat | 0 <= i < 5 :: q_seq'nat'_26__emit[i] == 0)
{
  var q_seq'nat'_0__emit_seq'nat'_1__emit : seq<nat> := q_seq'nat'_0__emit;
  // Forward Declaration
  var q_seq'seq'nat''_23__emit : seq<seq<nat>>;
  var q_seq'nat'_22__emit : seq<nat>;
  var q_seq'nat'_21__emit : seq<nat>;
  var q_seq'seq'nat''_20__emit : seq<seq<nat>>;
  var q_seq'nat'_19__emit : seq<nat>;
  var q_seq'nat'_18__emit : seq<nat>;
  var loc__loc__receiver_3_seq'unsupported'_17__emit : seq<real>;
  var q_seq'seq'nat''_16__emit : seq<seq<nat>>;
  var q_seq'nat'_15__emit : seq<nat>;
  var q_seq'nat'_14__emit : seq<nat>;
  var loc__loc__receiver_3_seq'unsupported'_13__emit : seq<real>;
  var q_seq'seq'nat''_12__emit : seq<seq<nat>>;
  var q_seq'nat'_11__emit : seq<nat>;
  var q_seq'nat'_10__emit : seq<nat>;
  var loc__loc__receiver_0_seq'unsupported'_9__emit : seq<real>;
  var loc__loc__receiver_0_phase_1__8__emit : seq<nat>;
  var loc__loc__receiver_0_phase_base_7__emit : nat;
  var q_seq'seq'nat''_6__emit : seq<seq<nat>>;
  var loc__loc__receiver_0_phase_1__5__emit : seq<nat>;
  var loc__loc__receiver_0_phase_base_4__emit : nat;
  var q_seq'nat'_3__emit : seq<nat>;
  var q_seq'nat'_2__emit : seq<nat>;
  // Revealing
  reveal Map();
  reveal Pow2();

  // Method Definition
  q_seq'nat'_3__emit := q_seq'nat'_0__emit_seq'nat'_1__emit[1..15];
  q_seq'nat'_2__emit := q_seq'nat'_0__emit_seq'nat'_1__emit[0..1];
  loc__loc__receiver_0_phase_1__5__emit := CastNorHad_Phase_1st( q_seq'nat'_2__emit );
  loc__loc__receiver_0_phase_base_4__emit := 2;
  assert |loc__loc__receiver_0_phase_1__5__emit| == 1;
  assert true;
  loc__loc__receiver_0_phase_base_7__emit :=
    loc__loc__receiver_0_phase_base_4__emit;
  loc__loc__receiver_0_phase_1__8__emit :=
    CastHadEn_Phase_1st( loc__loc__receiver_0_phase_1__5__emit
                       , loc__loc__receiver_0_phase_base_4__emit );
  q_seq'seq'nat''_6__emit := CastHadEn01_Ket1();
  loc__loc__receiver_0_seq'unsupported'_9__emit :=
    seq<real>( |q_seq'seq'nat''_6__emit|
             , (_) =>
               ( (((1) as real)) /
                 (((Pow2(|q_seq'seq'nat''_6__emit|)) as real)) ) );
  q_seq'nat'_11__emit := q_seq'nat'_3__emit[9..14];
  q_seq'nat'_10__emit := q_seq'nat'_3__emit[0..9];
  loc__loc__receiver_3_seq'unsupported'_13__emit :=
    loc__loc__receiver_0_seq'unsupported'_9__emit;
  q_seq'seq'nat''_12__emit := q_seq'seq'nat''_6__emit;
  q_seq'nat'_14__emit := q_seq'nat'_10__emit;
  q_seq'nat'_15__emit := q_seq'nat'_11__emit;
  for i := 0 to 9
    invariant |loc__loc__receiver_3_seq'unsupported'_13__emit| == 2
    invariant |q_seq'seq'nat''_12__emit| == 2
    invariant (forall j : nat | 0 <= j < 2 ::
      |q_seq'seq'nat''_12__emit[j]| == 1 + i)
    invariant (forall j : nat | 0 <= j < 2 ::
      (forall k : nat | 0 <= k < j :: q_seq'seq'nat''_12__emit[j][k] == j))
    invariant |q_seq'nat'_14__emit| == 9 - i
    invariant (forall k : nat | 0 <= k < 9 - i :: q_seq'nat'_14__emit[k] == 0)
    invariant |q_seq'nat'_15__emit| == 5
    invariant (forall i : nat | 0 <= i < 5 :: q_seq'nat'_15__emit[i] == 0)
  {
    loc__loc__receiver_3_seq'unsupported'_17__emit :=
      loc__loc__receiver_3_seq'unsupported'_13__emit;
    q_seq'seq'nat''_16__emit := q_seq'seq'nat''_12__emit;
    // begin false
    q_seq'nat'_19__emit := q_seq'nat'_14__emit[1..9 - i];
    q_seq'nat'_18__emit := q_seq'nat'_14__emit[0..1];
    q_seq'seq'nat''_20__emit :=
      Map( (lambda_x_7) => (lambda_x_7 + q_seq'nat'_18__emit)
         , q_seq'seq'nat''_16__emit );
    // end false
    // begin true
    q_seq'nat'_22__emit := q_seq'nat'_14__emit[1..9 - i];
    q_seq'nat'_21__emit := q_seq'nat'_14__emit[0..1];
    q_seq'nat'_21__emit :=
      q_seq'nat'_21__emit[0..-9 + i] +
      Map((x) => (x + 1), q_seq'nat'_21__emit[-9 + i..-8 + i]) +
      q_seq'nat'_21__emit[-8 + i..|q_seq'nat'_21__emit|];
    q_seq'seq'nat''_23__emit :=
      Map( (lambda_x_9) => (lambda_x_9 + q_seq'nat'_21__emit)
         , q_seq'seq'nat''_16__emit );
    // end true
    // begin true-false
    loc__loc__receiver_3_seq'unsupported'_17__emit :=
      loc__loc__receiver_3_seq'unsupported'_17__emit;
    q_seq'seq'nat''_20__emit := q_seq'seq'nat''_23__emit;
    // end true-false
    // Match Begin-End
    loc__loc__receiver_3_seq'unsupported'_17__emit :=
      loc__loc__receiver_3_seq'unsupported'_17__emit;
    q_seq'seq'nat''_16__emit := q_seq'seq'nat''_20__emit;
    q_seq'nat'_15__emit := q_seq'nat'_15__emit;
    q_seq'nat'_14__emit := q_seq'nat'_19__emit;
  }
  loc__loc__receiver_3_seq'unsupported'_25__emit :=
    loc__loc__receiver_3_seq'unsupported'_13__emit;
  q_seq'seq'nat''_24__emit := q_seq'seq'nat''_12__emit;
  q_seq'nat'_26__emit := q_seq'nat'_15__emit;
}
}
