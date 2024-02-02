# A Verified VPG Parser Generator

A parser generator for visibly pushdown grammars (VPGs) is implemented
and verified in the proof assistant [Coq](https://coq.inria.fr/) under
the folder `VPGParser/`. The parser generator is exported to OCaml
library `VerifiedParser.ml` with commands under the folder `Export/`.

## Requirements

```
Coq@8.16.1
```

## Build

The following command compiles the Coq library, exports the OCaml
library to a single file `VerifiedParser.ml`, and generates documentation for the Coq library. The command takes ~5
mins on Intel 9700 with 16 GB memory.

```Shell
make && make doc
```

## Overview

Given a VPG $G=(\Sigma,P,V,L_0)$, where $\Sigma$ is a set of terminals,
$V$ is a set of nonterminals, $P$ is a set of production rules, and
$L_0$ is the start nonterminal, this library provides a function $f$
that maps a string $s$ to a set $V$ of rule sequences
$v=[r_i]_{i=1..|s|},r_i\in P$; each sequence derives the string $s$ and
is called a _VPG parse tree_ of the string $s$.

$$f:(G,s)\mapsto V$$

The function $f$ is composed of three subfunctions, namely $p$,
$f_\text{init}$ and $\text{extraction}$:

$$f=\text{extraction}\circ f_\text{init} \circ p.$$

The subfunctions are briefly discussed as follows. The _parsing
function_ $p$ first generates a _forest_ $M$, a compression of all VPG
parse trees of the string $s$.

$$p: (G,s)\mapsto M$$ 

Let $M=m\cdot M'$, the _initialization extraction function_
$f_\text{init}$ then extracts the initial set $V_0$ of the partial VPG parse trees.

$$f_\text{init}: m\cdot M'\mapsto V_0$$

Finally, the _backward extraction function_ $\text{extraction}$ extracts
rules from the rest forest $M'$ and uses them to extend the partial
trees.

$$\text{extraction}: (V_0,M')\mapsto V$$

All functions are implemented and verified in the proof assistant
[Coq](https://coq.inria.fr/); the library is then exported to OCaml
(`VerifiedParser.ml`) for further utilization.

## What is verified

The verified properties of the parser generator are summarized in
Theorem `Property_VPG_Parser_Generator` in the module
`VPGParser/TimedExtraction.v`, declared as follows.

```Coq
Theorem Property_VPG_Parser_Generator:
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

The relation `Forest (m::M) T (w++[i])` formalizes the process to generate a forest $p(w)=M$ with the one-step version of the parsing function $p$ (also denoted as $p$): starting from the initial configuration $(m_0,\bot)$, reading the string $w$, and transferring to the final configuration $(m',T')$, the traces [$m,...,m']$ is the forest.

```Coq
Inductive Forest : (list CME) -> (list CME) -> (list symbol) -> Prop :=
| FInit: Forest [m0] [] []
| FInte i m M T w m' T': 
    Forest (m::M) T w
    -> (m', T') = p m T i
    -> Forest (m'::m::M) T' (w++[i]).
```

Back to the theorem, we can see that $m$ in the forest $m::M$ is first
extracted by $f_\text{init}$ to generate the initial set of partial parse trees $V_\text{init}$, then the rest
forest $M$ is extracted by the function $\text{extraction}$ to generate
the final set of parse trees $V_w$. The theorem includes three properties, discussed as follows.

1. $V_w$, conceptually a _set_ of VPG parse trees, is implemented as a
   _list_ of VPG parse trees. The first property `NoDup Vw` shows $V_w$
   has no duplicates, therefore can be viewed as a set.
2. The function $\text{extraction}$ has a monadic counterpart
   $\text{extraction}'$, which is verified to have the time complexity
   `cost_extraction`. The second property
   shows `cost_extraction}=O(|V_w||w|)`, i.e., $O(|w|)$ times the number of all valid parse trees. When
   $|V_w|\leq 1$, which is always the case for unambiguous grammars, it
   shows that the extraction function is linear-time.
3. The last property shows the correctness: a VPG parse tree $v$ is in
   $V_w$, iff the following relation holds.
   
   $$\text{Dm}\ L_0\ w\ v$$

   The relation $\text{Dm}$ ("major derivation") is called the _big-step
   derivation_ of the VPG parse trees; it defines how to "correctly"
   derive a VPG parse tree from the start nonterminal $L_0$. In the
   paper [1], the notation of `Dm` is $$L_0\Downarrow (w, v).$$ In Coq,
   the relation is defined as follows.

    ```Coq
        Inductive Dm : var -> list symbol -> list VE -> Prop :=
        | DEps : ∀ L, (in_rules (L, Alt_Epsilon) P) -> Dm L [] []
        | DLa : ∀ L a L1 w' pt', 
          (in_rules (L, Alt_Linear (Call a) L1) P)
          -> Dm L1 w' pt'
          -> Dm L (Call a::w') (Calv (PndCalE L a L1)::pt')
        | DLc : ∀ L c L1 w' pt', 
          (in_rules (L, Alt_Linear (Plain c) L1) P) 
          -> Dm L1 w' pt' 
          -> Dm L (Plain c::w') (Plnv (PlnE L c L1)::pt')
        | DLb : ∀ L b L1 w' pt', 
          (in_rules (L, Alt_Linear (Ret b) L1) P) 
          -> Dm L1 w' pt' 
          -> Dm L (Ret b::w') (Retv (PndRetE L b L1)::pt')
        | DMat : ∀ L a b L1 L2 w1 w2 pt1 pt2, 
          (in_rules (L, Alt_Match (a) (b) L1 L2) P) 
          -> Dm L1 w1 pt1
          -> Dm L2 w2 pt2
          -> Dm L ([Call a] ++ w1 ++ [Ret b] ++ w2) 
            ([Calv (MatCalE L a L1 b L2)]++pt1++
            [Retv (MatRetE L a L1 b L2)]++pt2).
    ```

    Because it works for general VPGs, the above definition has two more
    rules than the big-step relation for well-matched VPGs discussed in
    the paper [1], namely `DLa`, derivation for linear call rules, and
    `DLb`, derivation for linear return rules.

## Utilized axioms 

The library depends on two axioms, collected in the module type
`VPG`, defined as follows.

```Coq
Module Type VPG.
  Parameter L_0 : vpg_var.
  Parameter P : vpg.rules.

  Axiom A_VPG_Linear: ∀ L c L1,
    in_rules (L, Alt_Linear c L1) P
    -> (∃ u, L = V0 u)
    -> ∃ u1 i, L1 = V0 u1 /\ c=Plain i.

  Axiom A_VPG_Match: ∀ L a L1 b L2,
    in_rules (L, Alt_Match a b L1 L2) P
    -> (∃ u1, L1 = V0 u1) /\ 
      ((∃ u, L = V0 u) -> ∃ u2, L2 = V0 u2).
End VPG.
```

The type `VPG` requires a VPG $G$ has a start nonterminal $L_0$ and a
set of production rules $P$; $P$ implicitly declares the nonterminals
and terminals. The two axioms are not needed for well-matched VPGs; they
represent the two restrictions of general VPGs. For more details about
the restrictions, please refer to [1].

## How the properties are verified

Please refer to [VPGParser/README.md](VPGParser/README.md) for more
implementation details.

## Benchmarks

The benchmarks are located in `Benchmark/`.

## References

[1] Xiaodong Jia, Ashish Kumar, and Gang Tan. 2021. A derivative-based
parser generator for visibly Pushdown grammars. Proc. ACM Program. Lang.
5, OOPSLA, Article 151 (October 2021), 24 pages.
https://doi.org/10.1145/3485528
