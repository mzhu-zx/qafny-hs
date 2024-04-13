include "../../../../external//QPreludeUntyped.dfy"
include "../../../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../../../external//libraries/src/NonlinearArithmetic/Power2.dfy"
include "../../../../external//libraries/src/NonlinearArithmetic/Power.dfy"

// target Dafny version: 4.2.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2
import opened Power
import opened DivMod

method GHZ ( q_seq'nat'_0__emit : seq<nat> ) ( loc__loc__receiver_3_seq'unsupported'_25__emit : seq<real>
, q_seq'seq'nat''_24__emit : seq<seq<nat>>
, q_seq'nat'_26__emit : seq<nat> )
  
{
  var q_seq'nat'_0__emit_seq'nat'_1__emit : seq<nat> := q_seq'nat'_0__emit;
  // Forward Declaration
  var q_seq'seq'nat''_23__emit : seq<seq<nat>>;
  var q_seq'nat'_22__emit : seq<nat>;
  var q_seq'nat'_21__emit : seq<nat>;
  var q_seq'seq'nat''_20__emit : seq<seq<nat>>;
  var q_seq'nat'_19__emit : seq<nat>;
  var q_seq'nat'_18__emit : seq<nat>;
  var q_seq'seq'nat''_16__emit : seq<seq<nat>>;
  var q_seq'nat'_15__emit : seq<nat>;
  var q_seq'nat'_14__emit : seq<nat>;
  var q_seq'seq'nat''_12__emit : seq<seq<nat>>;
  var q_seq'nat'_11__emit : seq<nat>;
  var q_seq'nat'_10__emit : seq<nat>;
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
  loc__loc__receiver_0_phase_base_4__emit,
  loc__loc__receiver_0_phase_1__5__emit := (CastNorHad(q_seq'nat'_2__emit));
  loc__loc__receiver_0_phase_1__8__emit := loc__loc__receiver_0_phase_1__5__emit;
  loc__loc__receiver_0_phase_base_7__emit := CastHadEn_Phase_1st( loc__loc__receiver_0_phase_base_4__emit
  , loc__loc__receiver_0_phase_1__5__emit );
  q_seq'seq'nat''_6__emit := CastHadEn01_Ket1();
  loc__loc__receiver_0_seq'unsupported'_9__emit := seq<seq<real>>(|q_seq'seq'nat''_6__emit|, ( _ ) => ( (((1) as real)) / (((Pow2( |q_seq'seq'nat''_6__emit| )) as real)) ));
  q_seq'nat'_11__emit := q_seq'nat'_3__emit[9..14];
  q_seq'nat'_10__emit := q_seq'nat'_3__emit[0..9];
  q_seq'seq'nat''_12__emit := q_seq'seq'nat''_6__emit;
  q_seq'nat'_14__emit := q_seq'nat'_10__emit;
  q_seq'nat'_15__emit := q_seq'nat'_11__emit;
  for i := 0 to 9
    
  {
    loc__loc__receiver_3_seq'unsupported'_17__emit := loc__loc__receiver_3_seq'unsupported'_13__emit;
    q_seq'seq'nat''_16__emit := q_seq'seq'nat''_12__emit;
    // begin false
    q_seq'nat'_19__emit := q_seq'nat'_14__emit[1..9 - i];
    q_seq'nat'_18__emit := q_seq'nat'_14__emit[0..1];
    q_seq'seq'nat''_20__emit := Map( ( lambda_x_7 ) => ( lambda_x_7 + q_seq'nat'_18__emit )
    , q_seq'seq'nat''_16__emit );
    // end false
    // begin true
    q_seq'nat'_22__emit := q_seq'nat'_14__emit[1..9 - i];
    q_seq'nat'_21__emit := q_seq'nat'_14__emit[0..1];
    q_seq'nat'_21__emit := q_seq'nat'_21__emit[0..-9 + i] + Map( (x) => (x + 1)
    , q_seq'nat'_21__emit[-9 + i..-8 + i] ) + q_seq'nat'_21__emit[-8 + i..|q_seq'nat'_21__emit|];
    q_seq'seq'nat''_23__emit := Map( ( lambda_x_9 ) => ( lambda_x_9 + q_seq'nat'_21__emit )
    , q_seq'seq'nat''_16__emit );
    // end true
    // begin true-false
    q_seq'seq'nat''_20__emit := q_seq'seq'nat''_20__emit + q_seq'seq'nat''_23__emit;
    // end true-false
    // Match Begin-End
    q_seq'seq'nat''_16__emit := q_seq'seq'nat''_20__emit;
    q_seq'nat'_14__emit := q_seq'nat'_19__emit;
  }
  loc__loc__receiver_3_seq'unsupported'_13__emit := loc__loc__receiver_3_seq'unsupported'_25__emit;
  q_seq'seq'nat''_12__emit := q_seq'seq'nat''_24__emit;
  q_seq'nat'_15__emit := q_seq'nat'_26__emit;
}
}
