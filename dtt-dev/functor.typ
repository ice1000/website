#import "config.typ": *
#import "@preview/fletcher:0.4.3" as fletcher: diagram, node, edge
#show: dtt.with(title: "Outside structures")
#set quote(block: true)

= Introduction

The goal of this chapter is to defined well-typed translations between type theories, aka compilers.

Before talking about translations between type theories,
we first need to make it explicit that what data give rise to a type theory, and then we define how to translate between them.

= Conventions

We consider a type theory to be a #cross-link("subst")[substitution calculus] plus a set of postulated rules,
denoted using caligraphic letters or bold font words, e.g. $cal(A), cal(B)$, or $bold("TT")$.

In the presence of multiple type theories, we write $Γ ⊢^cal(A) ...$ to mean that this judgment happens in type theory $cal(A)$.

Recall in #cross-link("struct-1")[last chapter] we have introduced a couple of _structures_ of type theories, defined to be having some data and the ability to derive some rules.
When postulating rules, we might just say "$cal(A)$ has #cross-link("struct-1", reference: <def_product>)[product type]" to say that we are postulating all the rules needed by product type in $cal(A)$.

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

- A mapping from types $Γ ⊢^cal(A) A$ into the types in $cal(B)$, such that $[| Γ |]_cal(F) ⊢^cal(B) [| A |]_cal(F)$ is derivable, where $[|Γ|]_cal(F)$ is iterated translation of types inside $Γ$,
- A mapping from terms $Γ ⊢^cal(A) t : A$ into terms in $cal(B)$, such that $[| Γ |]_cal(F) ⊢^cal(B) [| t |]_cal(F) : [| A |]_cal(F)$ is derivable;

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

Normally, the rules term and type formers are always postulated, not proved to be admissible,
since we have in mind that typing derivations are in correspondence with proof terms, a canonical representation of its _derivation_ -- directly indicates the existence of a derivation.

In the definition of a compiler, we require that the translated judgments are derivable,
not admissible, and the rationale is due to the following construction we wish to be well-defined:

#construction("Composition")[
If $cal(F):cal(A) → cal(B)$ and $cal(G):cal(B) → cal(C)$ are compilers,
then the _composition_ of them, denoted $cal(G) ∘ cal(F):cal(A) → cal(C)$, is a compiler,
defined as follows:

1. For $Γ ⊢^cal(A) A$, define $[| A |]_(cal(G) ∘ cal(F)) = [| [| A |]_cal(F) |]_cal(G)$,
2. For $Γ ⊢^cal(A) t : A$, define $[| t |]_(cal(G) ∘ cal(F)) = [| [| t |]_cal(F) |]_cal(G)$.

The judgmental equalities hold immediately.
]

If we only require the judgmental equalities to be admissible, they wouldn't be further preserved under translation.

#construction("Identity")[
For every type theory $cal(A)$, there exists an _identity compiler_ $cal(I):cal(A) → cal(A)$
such that $[| A |]_cal(I) = A$ and $[| t |]_cal(I) = t$.
]

Then, it is tempting to state the unital and associativity laws for compilers,
but to do so we first need:

+ A notion of equality between compilers,
+ which requires the notion of equivalence between type theories,
+ which requires the notion of equivalence between types.

To start, we need to specify the equivalence between $Γ⊢A$ and $Γ⊢B$,
which we intend to do by defining a type-theoretic bijection between their terms.

// To define a map from $A$ to $B$, it is tempting to write $Γ,x:A ⊢ b:B$,
// but this does not make type sense, because it presupposes $Γ,x:A⊢B$, which is not true!
// So, instead we have to do $Γ,x:A ⊢ b:B[π_A]$, similarly we have $Γ,x:B ⊢ a:A[π_B]$.

// Then, we want to compose them in an appropriate way. To substitute $a$ into $b$, we need a substitution whose codomain is $Γ,x:A$. However, we can only afford to provide $b$ as a substitution with codomain $Γ,x:B,y:A[π_B]$ (by appending it to an identity substitution),
// and by #cross-link("subst", reference: <def_exchange>)[exchange]
// we know it's equivalent to $Γ,x:A,y:B[π_A]$ by a substitution $ex(B,A)$.

TODO

= Conclusion

In this chapter, we defined the notion of a compiler between type theories, which is a sensible _structure-preserving_ map between them, as it preserves the derivability of judgments.
