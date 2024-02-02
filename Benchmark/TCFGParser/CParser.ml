(** Interfaces of the Coq Parser. *)

open CoqParser.VerifiedParser
include Coq_vpg

module type VPG = VPG

(** an example VPG  *)
(* module G : VPG = struct
  let coq_L_0 = V0 [ 'L'; '0' ]
  let coq_P = []
end *)

(** the types of functions in a VPG parser generator *)
module type CoqParserType = sig
  open DEF

  val p : coq_ME -> coq_ME list -> Coq_vpg.symbol -> coq_ME * coq_ME list
  val f_init : coq_ME -> (coq_VE list * coq_RetEdge list) list

  val f_b :
    coq_ME ->
    (coq_VE list * coq_RetEdge list) list ->
    (coq_VE list * coq_RetEdge list) list

  val extraction :
    coq_ME list ->
    (coq_VE list * coq_RetEdge list) list ->
    (coq_VE list * coq_RetEdge list) list c
end

module CParser (G : VPG) : CoqParserType = struct
  module P = TimedExtraction (G)

  let p =
    P.TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup
    .Transducer
    .TimedSets
    .Parser
    .p

  let f_init =
    P.TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup
    .Transducer
    .Transducer2
    .f_init

  let f_b =
    P.TimedExtractionRet.TimedExtractionCal.TimedExtractionPln.ExtractionWNoDup
    .Transducer
    .Transducer2
    .f_b

  let extraction = P.extraction'
end
