(** Export OCaml library from the Coq implementation.
     The usage is documented in Makefile. *)

Require Import TimedExtraction.

(** Recursively export all modules *)
Extraction "VerifiedParser" TimedExtraction.
