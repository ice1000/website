#import "config.typ": *
#import "@preview/fletcher:0.4.3" as fletcher: diagram, node, edge
#show: dtt.with(title: "Limits")

#let struct-2-fulltext = [
== Introduction

The goal of this chapter is to revisit the structures defined in #cross-link("struct-1")[Structures I] with an eye on generalization.

== Structures, revisited

We start the section by a reflection on the definition of #cross-link("struct-1", reference: <def_unit>)[having a unit type].
For a type theory to have a unit type, the following needs to be true:

For every context $Γ$,
+ there is a type $Γ ⊢ top$,
+ there is a term $Γ ⊢ ★ : top$
  such that every term of this type is equal to it,
+ and this whole thing is preserved by substitution.

For product types, we can rephrase its definition in a similar way,
but with the presence of rule premises, they are more complicated:

For every context $Γ$ and types $Γ ⊢ A$ and $Γ ⊢ B$,
+ there is a type $Γ ⊢ A × B$,
+ for every pair of terms $Γ ⊢ t : A$ and $Γ ⊢ u : B$, there is a term $Γ ⊢ ⟨t, u⟩ : A × B$
  such that every term of this type can be written as such a pair,
+ and this whole thing is preserved by substitution.

Note that the fact that all terms can be written as such a pair is known as all terms _factor through_ the introduction rule.
Similarly for the empty type, all terms in contexts where $bot$ is present _factor through_ the elimination rule.

There seems to be a lot of things in common:

For every context $Γ$ and types $Γ ⊢ 🤔$,
+ there is a type $Γ ⊢ ✨$,
+ for every tuple of terms $Γ ⊢ ... : 🤔$, there is a term $Γ ⊢ ... : ✨$
  such that every term of this type factor through its introduction,
+ and this whole thing is preserved by substitution.

Now, the real question arise: can we generalize this and how do we do that?

== Compiler as type

We start by thinking about products.
Given any $Γ⊢A$ and $Γ⊢B$, and let's think about $Γ⊢X$ with two _pseudo-projections_:
$ Γ,x:X ⊢ a: A #h(2em) Γ,x:X ⊢ b: B $
We pack them up and write it as $(X, a, b)$.
In what case do we consider $X$ to be a product of $A$ and $B$?

The generalization is very hard to motivate, but here is the construction.
Consider all such product-like things $(X, a, b)$.
Assuming the product $A×B$ exists, so that must be one of those $X$'s,
and the packed data is $(A×B, x.1, x.2)$.
Then, for every $X$, there must exist a _unique_ term:
$ Γ, x:X ⊢ h : A×B $
such that:
$ Γ, x:X ⊢ a ≡ h.1 : A \
  Γ, x:X ⊢ b ≡ h.2 : B
  $
where $h.1$ is the result of the substitution $x.1 [h slash x]$, and similarly for $h.2$.
The idea is that constructing a term of type $A×B$ must go through its introduction rule,

We can diagramize the above conditions.
In context $Γ$, we have:
#align(center)[#diagram(cell-size: 15mm, $
  &X edge("lb", a, ->)
     edge("rb", b, ->)
     edge("d", h, "-->")
   & \
  A &A×B edge("l", .1, ->)
      edge("r", .2, ->)
  & B
$)]
TODO
]
#struct-2-fulltext
