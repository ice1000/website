#import "config.typ": *
#show: dtt.with(title: "Outside structures")

= Introduction

The goal of this chapter is to defined well-typed translations between type theories, aka compilers.

Before talking about translations between type theories,
we first need to make it explicit that what data give rise to a type theory, and then we define how to translate between them.

= Conventions

We consider a type theory to be a #cross-link("/dtt-dev/subst.typ")[substitution calculus] plus a set of postulated rules,
denoted using caligraphic letters, e.g. $cal(A), cal(B)$.

In the presence of multiple type theories, we write $Γ ⊢^cal(A) ...$ to mean that this judgment happens in type theory $cal(A)$.

Recall in #cross-link("/dtt-dev/struct-1.typ")[last chapter] we have introduced a couple of _structures_ of type theories, defined to be having some data and the ability to derive some rules.
When postulating rules, we might just say "$cal(A)$ has #cross-link("/dtt-dev/struct-1.typ", reference: <def_product>)[product type]" to say that we are postulating all the rules needed by product type in $cal(A)$.

The following are some example definitions of type theories:

#example("Empty type theory")[The empty type theory has the empty set of postulated rules.]
#lemma[In the empty type theory, there is only one context -- the empty one.]
#example("Unit type theory")[The unit type theory has a unit type.]
#lemma[In the unit type theory, all contexts except the empty one are isomorphic.]

= Translations

#definition("Compiler")[
A _compiler_ from type theory $cal(A)$ to type theory $cal(B)$
is a pair of functions:

TODO
]
