# A Verified VPG Parser Generator: Implementation Details

This file discusses the roles of different modules, i.e., the files
`*.v`, in the Coq implementation. Additionally, the Coq documentation
for each module is generated with the following command, which generated
HTML documentation files in the folder `../Doc`.

```Shell
cd .. && make doc
```

## Overview

As discussed in [../README.md](../README.md), the library verifies the
following property in `TimedExtraction.v`.

```Coq
(** The property of the end-to-end VPG parser *)
Theorem Property_VPG_Parser_Generator:
(** cost of extraction = O((k·m+b1)·|w|+b2) *)
∃ k b1 b2,
∀ m M T w i, Forest (m::M) T (w++[i]) ->
    let Vinit := f_init m in
    let Vw := extraction M Vinit in
    (** 1. Vw has no duplicates *)
    NoDup Vw /\
    (** 2. The time cost is O(k·|Vw|·|w|) *)
    cost_extraction M Vinit <= (k * |Vw| + b1) * |w++[i]| + b2 /\
    (** 3. The correctness *)
    (∀ v, (∃ I, In (v, I) Vw) <-> DM.Dm L_0 (w ++ [i]) v).
```

The first and the second properties relate to the time complexity, and
are therefore independent from the third property, which relates to the
correctness. The correctness property is discussed first, followed by
the ones for the time complexity.

## The Correctness

The correctness is based on $V_w$, where 
$$V_w=f(w)=\text{extraction}\circ f_\text{init}\circ p(w).$$

The related properties of the above functions are verified in the
following modules. Please refer to the generated Coq documentation for
more details.

```Shell
./ForwardSmallStep.v
./BackwardSmallStep.v
./Dbx.v
./GenForest.v
./Transducer.v
```

The ideas of the proofs are summarized as follows.

1. The parsing function $p$ derives a forest $M$ (in the relation
   `Forest w T M`), defined in `GenForest.v`.
2. Intuitively, the forest `M` is a compression of a set of parse trees.
   Those parse trees are formalized by the _forward small-step
   derivation_, defined in `ForwardSmallStep.v`.
3. The extraction function $\text{extraction}$ maintains a set of parse
   trees during the extraction. Those parse trees are formalized by the
   _backward small-step derivation_, defined in `BackwardSmallStep.v`. 
4. The correctness is based on the _big-step derivation_ `Dm L v w`,
   which defines how to correctly derive the string $w$ from the
   nonterminal $L$ with the rule sequence $v$.
5. We show the correctness by proving that during the extraction, each
   parse tree $v$ in $V$ has a counterpart $v'$, which together satisfy
   `Dm L0 (v'++v) w`, in the module `Transducer.v`.


## The Time Complexity

We wrap the parsing and extraction functions in monadic functions which store the time cost, with the help of a monadic library [1]. The final result is summarized in the module `TimedExtraction.v`. Please refer to the generated Coq documentation for more details.

```Shell
./TimedSets.v
./PreTimed.v
./Monad.v
./MonadicUtils.v
./ExtractionW.v
./TimedRunPDA.v
./TimedExtractionPln.v
./TimedExtractionCal.v
./TimedExtractionRet.v
./TimedExtraction.v
```

[1] Jay McCarthy, Burke Fetscher, Max New, Daniel Feltey, and Robert
Bruce Findler. 2016. A Coq library for internal verification of
running-times. In International Symposium on Functional and Logic
Programming. Springer, 144–162.