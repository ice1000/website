#import "config.typ": *
#import "@preview/fletcher:0.4.3" as fletcher: diagram, node, edge
#show: dtt.with(title: "Outside structures")

= Introduction

The goal of this chapter is to defined well-typed translations between type theories, aka compilers.

Before talking about translations between type theories,
we first need to make it explicit that what data give rise to a type theory, and then we define how to translate between them.

= Conventions

We consider a type theory to be a #cross-link("/dtt-dev/subst.typ")[substitution calculus] plus a set of postulated rules,
denoted using caligraphic letters or bold font words, e.g. $cal(A), cal(B)$, or $bold("TT")$.

In the presence of multiple type theories, we write $Γ ⊢^cal(A) ...$ to mean that this judgment happens in type theory $cal(A)$.

Recall in #cross-link("/dtt-dev/struct-1.typ")[last chapter] we have introduced a couple of _structures_ of type theories, defined to be having some data and the ability to derive some rules.
When postulating rules, we might just say "$cal(A)$ has #cross-link("/dtt-dev/struct-1.typ", reference: <def_product>)[product type]" to say that we are postulating all the rules needed by product type in $cal(A)$.

The following are some example definitions of type theories:

#example[
- The empty type theory $bold(0)$ has the empty set of postulated rules.
- The unit type theory $bold(1)$ has a unit type.
- Alternatively, another unit type theory has a unit type and product types.
] <ex_empty_unit_fp>
#lemma[In the empty type theory, there is only one context -- the empty one.]
#lemma[In the unit type theory, all contexts except the empty one are isomorphic.]

= Translations

#definition("Compiler")[
A _compiler_ from type theory $cal(A)$ to type theory $cal(B)$, denoted $cal(F):cal(A) → cal(B)$,
is a pair of functions, called _translations_, both denoted $[| - |]_cal(F)$,
where for input $A$, it produces output $[| A |]_cal(F)$:

- A mapping from types $Γ ⊢^cal(A) A$ into the types in $cal(B)$, denoted $[| Γ |]_cal(F) ⊢^cal(B) [| A |]_cal(F)$, where $[|Γ|]_cal(F)$ is iterated translation of types inside $Γ$,
- A mapping from terms $Γ ⊢^cal(A) t : A$ into terms in $cal(B)$, denoted $[| Γ |]_cal(F) ⊢^cal(B) [| t |]_cal(F) : [| A |]_cal(F)$;

such that:

- If $Γ ⊢^cal(A) A ≡ B$ is derivable, then $[| Γ |]_cal(F) ⊢^cal(B) [| A |]_cal(F) ≡ [| B |]_cal(F)$ is derivable,
- If $Γ ⊢^cal(A) t ≡ u : A$ is derivable, then $[| Γ |]_cal(F) ⊢^cal(B) [| t |]_cal(F) ≡ [| u |]_cal(F) : [| A |]_cal(F)$ is derivable.
] <def_compiler>

When there is only one compiler in the context, we might omit the subscript $cal(F)$.

Observe that presuppositions commute with compilations:

#align(center)[#diagram(cell-size: 15mm, $
  Γ ⊢^cal(A) t: A
    edge("rr", #[presupposes])
    edge("d", [| - |], ->)
    && Γ ⊢^cal(A) A
    edge("d", [| - |], ->) \
  [| Γ |] ⊢^cal(B) [| t |] : [| A |]
    edge("rr", #[presupposes])
    && [| Γ |] ⊢^cal(B) [| A |]
$)]

So, when translating the rules, we do not have to do additional work to ensure that the presuppositions are satisfied.

#example[
For every type theory $cal(A)$, there exists a compiler from $cal(A)$ to the unit type theory $bold(1)$ (@ex_empty_unit_fp), by compiling all types and terms as the unit type and its introduction rule.
]
#example[
For every type theory $cal(A)$, there exists a compiler from the empty type theory $bold(0)$ to $cal(A)$, because there is nothing to compile.
]

= Structures as compilers

We start the section by observing the following fact.

#lemma[
To say a type theory $cal(A)$ has a unit type, it suffice to construct a compiler from the unit type theory $bold(1)$ to $cal(A)$.
] <lem_unit_compile>
#proof[
It suffice to choose an assignment of $top$ and $★$ such that the rules are satisfied.

Suppose the unit type in $bold(1)$ consists of $Γ ⊢^bold(1) top$ and $Γ ⊢^bold(1) ★ : top$, then by the provided compiler, their compilation results give rise to the desired data and judgmental equalities.
]

#lemma[
To say a type theory $cal(A)$ has an empty type, it suffice to construct a compiler from a type theory with only the empty type to $cal(A)$.
]
#proof[Similar to @lem_unit_compile.]

We can even do the same for product types, but that will be slightly harder,
and also motivates the use of derivability in the definition of a compiler @def_compiler.

#lemma[
To say a type theory $cal(A)$ has product types, it suffice to construct a compiler from the type theory with only products $bold("FP")$ to $cal(A)$.
]
#proof[
It suffice to choose an assignment of $Γ ⊢^bold("FP") A × B$, its introduction and elimination.

TODO
]

