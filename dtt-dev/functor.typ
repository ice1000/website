#import "config.typ": *
#import "@preview/fletcher:0.4.3" as fletcher: diagram, node, edge
#show: dtt.with(title: "Outside structures")
#set quote(block: true)

#let functor-fulltext = [
== Introduction

The goal of this chapter is to defined well-typed translations between type theories, aka compilers.

Before talking about translations between type theories,
we first need to make it explicit that what data give rise to a type theory, and then we define how to translate between them.

== Conventions

We consider a type theory to be a #cross-link("subst")[substitution calculus] plus a set of postulated rules,
denoted using bold font, e.g. $bold(A), bold(B)$, or $bold("TT")$.

In the presence of multiple type theories, we write $Γ ⊢^bold(A) ...$ to mean that this judgment happens in type theory $bold(A)$.

Recall in #cross-link("struct-1")[last chapter] we have introduced a couple of _structures_ of type theories, defined to be having some data and the ability to derive some rules.
When postulating rules, we might just say "$bold(A)$ has #cross-link("struct-1", reference: <def_product>)[product type]" to say that we are postulating all the rules needed by product type in $bold(A)$.

The following are some example definitions of type theories:

#example[
- The empty type theory $bold(0)$ has the empty set of postulated rules.
- The unit type theory $bold(1)$ has a unit type.
- Alternatively, another unit type theory has a unit type and product types.
] <ex_empty_unit_fp>
#lemma[In the empty type theory, there is only one context -- the empty one.]
#lemma[In the unit type theory, all contexts except the empty one are isomorphic.]

== Translations

#definition("Compiler")[
A _compiler_ from type theory $bold(A)$ to type theory $bold(B)$, denoted $bold(F):bold(A) → bold(B)$, consists of the following data:

+ A context $Δ$ in $bold(B)$, which we map the empty context in $bold(A)$ to,
+ A pair of functions, called _translations_, both denoted $[| - |]_bold(F)$,
  i.e. for input $A$, it produces output $[| A |]_bold(F)$, maps the types and terms from $bold(A)$ to $bold(B)$.
3. In addition to that, we define $[| Γ |]$ to be iteratively translating the types inside $Γ$ and push them onto $Δ$ -- the translation of the empty context;

such that:

+ For $Γ ⊢^bold(A) A$, the judgment $[| Γ |]_bold(F) ⊢^bold(B) [| A |]_bold(F)$ must be derivable,
+ For $Γ ⊢^bold(A) t : A$, the judgment $[| Γ |]_bold(F) ⊢^bold(B) [| t |]_bold(F) : [| A |]_bold(F)$ must be derivable,
+ If $Γ ⊢^bold(A) A ≡ B$ is derivable, then $[| Γ |]_bold(F) ⊢^bold(B) [| A |]_bold(F) ≡ [| B |]_bold(F)$ is derivable,
+ If $Γ ⊢^bold(A) t ≡ u : A$ is derivable, then $[| Γ |]_bold(F) ⊢^bold(B) [| t |]_bold(F) ≡ [| u |]_bold(F) : [| A |]_bold(F)$ is derivable.
] <def_compiler>

By default, we assume the empty context is translated into the empty context.

When there is only one compiler in the context, we might omit the subscript $bold(F)$.

Observe that presuppositions commute with compilations:

#align(center)[#diagram(cell-size: 15mm, $
  Γ ⊢^bold(A) t: A
    edge("rr", #[presupposes])
    edge("d", [| - |], ->)
    && Γ ⊢^bold(A) A
    edge("d", [| - |], ->) \
  [| Γ |] ⊢^bold(B) [| t |] : [| A |]
    edge("rr", #[presupposes])
    && [| Γ |] ⊢^bold(B) [| A |]
$)]

So, when translating the rules, we do not have to do additional work to ensure that the presuppositions are satisfied.

#example[
For every type theory $bold(A)$, there exists a compiler from $bold(A)$ to the unit type theory $bold(1)$ (@ex_empty_unit_fp), by compiling all types and terms as the unit type and its introduction rule.
]
#example[
For every type theory $bold(A)$, there exists a compiler from the empty type theory $bold(0)$ to $bold(A)$, because there is nothing to compile.
]

Normally, the rules term and type formers are always postulated, not proved to be admissible,
since we have in mind that typing derivations are in correspondence with proof terms, a canonical representation of its _derivation_ -- directly indicates the existence of a derivation.

In the definition of a compiler, we require that the translated judgments are derivable,
not admissible, and the rationale is due to the following construction we wish to be well-defined:

#construction("Composition")[
If $bold(F):bold(A) → bold(B)$ and $bold(G):bold(B) → bold(C)$ are compilers,
then the _composition_ of them, denoted $bold(G) ∘ bold(F):bold(A) → bold(C)$, is a compiler,
defined as follows:

1. For $Γ ⊢^bold(A) A$, define $[| A |]_(bold(G) ∘ bold(F)) = [| [| A |]_bold(F) |]_bold(G)$,
2. For $Γ ⊢^bold(A) t : A$, define $[| t |]_(bold(G) ∘ bold(F)) = [| [| t |]_bold(F) |]_bold(G)$.

The judgmental equalities hold immediately.
]

If we only require the judgmental equalities to be admissible, they wouldn't be further preserved under translation.

#construction("Identity")[
For every type theory $bold(A)$, there exists an _identity compiler_ $id_bold(A) :bold(A) → bold(A)$
such that $[| A |]_id_bold(A) = A$ and $[| t |]_id_bold(A) = t$.]
The use of the keyword $id$ is intentional not bold to be consistent with other identities.

Then, it is tempting to state the unital and associativity laws for compilers,
but to do so we first need a notion of equality between compilers,
which is roughly that they send the same types and terms to the same types and terms.

However, this is not immediately easy, because we care about using types abstractly,
not caring how they are implemented,
so for instance if two compilers are translating something using a unit type,
one uses a distinguished unit type and the other uses a unit type implemented by some other types,
we still consider them to be the same.

== Equivalences

To start, we need to specify the equivalence between $Γ⊢A$ and $Γ⊢B$,
which we intend to do by defining a type-theoretic bijection between their terms.

#definition("Type isomorphism")[
For types $Γ⊢A$ and $Γ⊢B$, a _type isomorphism_ (or _isomorphism_ for short) between them is a pair of terms $Γ,x:A ⊢ b:B$ and $Γ,x:B ⊢ a:A$ such that the following equations are derivable:
$ Γ,x:A ⊢ x ≡ a[b slash x] : A \
  Γ,x:B ⊢ x ≡ b[a slash x] : B $
We denote isomorphic type as a judgment $Γ⊢A ≃ B$.
]

We wish isomorphic types to _behave_ the same in type theory.

Then, we can talk about the equivalence between compilers:

#definition("Equivalent compilers")[
Two compilers $bold(F):bold(A) → bold(B)$ and $bold(G):bold(A) → bold(B)$ are _equivalent_ if for every type $Γ ⊢^bold(A) A$, we have:

+ a context isomorphism $[| Γ |]_bold(F) ⊢ σ : [| Γ |]_bold(G)$,
+ a type isomorphism $[| Γ |]_bold(F) ⊢ [| A |]_bold(F) ≃ [| A |]_bold(G) [σ]$.

We denote equivalent compilers as $bold(F) ≃ bold(G)$.]

#lesson[It is common that instances of a type are usually infinite,
and in that case they are always countable,
as the terms we an write down are essentially _abstract syntax trees_, and trees are countable.

However, there will still be infinite types that are not isomorphic,
since the definition of type isomorphism is an _internal_ isomorphism,
i.e. the isomorphism needs to be _inside_ the type theory.]

Then, we can define the desired unital and associativity laws for compilers:

#lemma[For compiler $bold(F):bold(A) → bold(B)$, we have:
$ (bold(F) ∘ id_bold(A)) ≃ (id_bold(B) ∘ bold(F)) ≃ bold(F) $]
#lemma[For compilers $bold(F):bold(A) → bold(B)$, $bold(G):bold(B) → bold(C)$, and $bold(H):bold(C) → bold(D)$, we have:
$ bold(H) ∘ (bold(G) ∘ bold(F)) ≃ (bold(H) ∘ bold(G)) ∘ bold(F) $]

We also need to establish the equivalence between types theories,
and to do so we need to consider the following:

+ We wish the equivalence to be weak:
  using different implementations of an "abstract" type should not affect the equivalence,
+ If we translate $Γ⊢^bold(A) A$ into $Γ' ⊢^bold(B) A'$, we wish the terms to be translated so that:
  + Different terms get translated into different terms,
  + Every term of $A'$ is the translation of some term of $A$.

Putting all of these conditions together, we can form a sensible notion of equivalence between type theories.

// Essentially surjective
#definition("Surjective")[We say a compiler $bold(F):bold(A) → bold(B)$ to be _surjective_
if for every type $Γ' ⊢^bold(B) B$ there exists a type $Γ ⊢^bold(A) A$ such that:
+ there exists a context isomorphism $Γ' ⊢ σ : [| Γ |]_bold(F)$,
+ $Γ' ⊢ B ≃ [| A |]_bold(F)[σ]$.]

// Fully faithful
#definition("Injective")[Consider a compiler $bold(F):bold(A) → bold(B)$ and a type $Γ ⊢^bold(A) A$.
We say $bold(F)$ to be:

+ _full_ if for every $[| Γ |] ⊢^bold(B) u : [| A |]$,
  there exists $Γ ⊢^bold(A) v : A$ such that $[| Γ |] ⊢^bold(B) u ≡ [| v |] : [| A |]$,
+ _faithful_ if $[| Γ |] ⊢^bold(B) [| u |] ≡ [| v |] : [| A |]$ implies $Γ ⊢^bold(A) u ≡ v : A$.

A compiler is _injective_ if it is both full and faithful.]

#definition("Equivalence")[We say a compiler to be an equivalence between type theories if it is surjective and injective.]

== Conclusion

In this chapter, we defined the notion of a compiler between type theories, which is a sensible _structure-preserving_ map between them, as it preserves the derivability of judgments.

Then, we described a couple of properties of compilers, and used them to define equivalences between type theories.
]
#functor-fulltext
