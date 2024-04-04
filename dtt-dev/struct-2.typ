#import "config.typ": *
#import "@preview/fletcher:0.4.3" as fletcher: diagram, node, edge
#let cedge(..args) = edge(label-side: center, ..args)
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

== Raw structures

We start by thinking about products.
Given any $Γ⊢A$ and $Γ⊢B$, we may rephrase the introduction of product $A×B$ as having another type $Γ⊢X$ with two _pseudo-projections_:
$ Γ,x:X ⊢ a: A #h(2em) Γ,x:X ⊢ b: B $
which gives me back the original $A$ and $B$.
This motivates the following definition.

// Cones for products
#definition("Raw product")[
Given any $Γ⊢A$ and $Γ⊢B$. A _raw product_ consists of the following data:
+ A type $Γ⊢X$,
+ Two terms $Γ,x:X ⊢ a: A$ and $Γ,x:X ⊢ b: B$.
We denote a raw product as $(X, a, b)$.
]

Then, the product $A×B$ is something we can always use these pieces of information to introduce an instance with, like this:
$ Γ,x:X ⊢ ⟨a,b⟩ : A×B $
Also note that the product $A×B$ can also be used to make a "raw product", namely $(A×B, x.1, x.2)$.
The special feature of this legitimate product is that it has an introduction rule that transforms any raw product into it.

Now, we can redefine the product without assuming its pre-existing rules.

#definition("Product")[
The product $(A×B,x.1,x.2)$ is a raw product such that
for every other raw product $(X,a,b)$, there exists a _unique_ term, called the _constructor_:
$ Γ, x:X ⊢ h : A×B $
such that:
$ Γ, x:X ⊢ a ≡ h.1 : A \
  Γ, x:X ⊢ b ≡ h.2 : B
  $
where $h.1$ is the result of the substitution $x.1 [h slash x]$, and similarly for $h.2$.
] <def_ct_product>
The idea is that constructing a term of type $A×B$ must go through its introduction rule,

We can diagramize the conditions in @def_ct_product as a commutative diagram.
In context $Γ$, we have:
#align(center)[#diagram(cell-size: 15mm, $
  &X cedge("lb", a, ->)
     cedge("rb", b, ->)
     cedge("d", h, "-->")
   & \
  A &A×B cedge("l", .1, ->)
      cedge("r", .2, ->)
  & B
$)]

This is rather like _characterizing_ the product type, instead of _defining_ it.

Now, it is tempting to define another type in a similar vibe.
Let's try the unit type and the extensional equality.

#definition("Raw unit")[
A _raw unit_ consists of the following data:
+ A type $Γ⊢X$,
+ A term $Γ⊢u: X$.
We denote a raw unit as $(X, u)$.
]

Then $(top, ★)$ is an instance of such a raw unit,
and we can characterize the unit type as follows:

#definition("Unit")[
The unit type is a raw unit such that
for every other raw unit $(X,u)$, there exists a _unique_ term, called the _constructor_:
$ Γ ⊢ h : top $
such that:
$ Γ ⊢ u ≡ h : top $
] <def_ct_unit>

It is clear that this coincides with the original definition of the unit type,
where $h$ is just another name for $★$!

TODO
]
#struct-2-fulltext
