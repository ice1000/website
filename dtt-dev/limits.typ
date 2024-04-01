#import "@preview/ctheorems:1.1.2": *
#show: thmrules.with(qed-symbol: $square$)

#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#let lemma = thmbox("lemma", "Lemma", fill: rgb("#eeffee"))
#let definition = thmbox("definition", "Definition", fill: rgb("#DFF9FF"))
#let proof = thmproof("proof", "Proof")
#let example = thmbox("example", "Example").with(fill: rgb("#f7f7fd"))
#let mybot = box(sym.bot)

#import "/book.typ": book-page
#show: book-page.with(title: "Finite Limits")

= Dependent Theory of Types

This is a series of extremely syntax-minded development on some meta-level dependent type theory,
which I wish to convey an interesting perspective.

The type theory I consider here is not designed to be implementable (i.e. have decidable type checking) or practical, but rather intended to be a reasoning framework about constructions.

== Preliminary Notions

#definition("Judgment schema")[
We assume the following judgment schemas of type theories:

- $Γ ⊢$ means $Γ$ is a well-formed context.
- $Γ ⊢ A$ means $A$ is a well-typed type in context $Γ$.
- $Γ ⊢ A ≡ B$ means $A$ and $B$ are equal types in $Γ$.
- $Γ ⊢ a : A$ means $a$ is a well-typed term of type $A$ in $Γ$.
- $Γ ⊢ a ≡ b : A$ means $a$ and $b$ are equal terms of type $A$ in $Γ$.
- $Γ ⊢ σ : Δ$ means $σ$ is a substitution object from $Γ$ to $Δ$.
- $Γ ⊢ σ ≡ τ : Δ$ means $σ$ and $τ$ are equal substitution objects from $Γ$ to $Δ$.
] <def_judgment>

In fact, we don't necessarily need $Γ ⊢ A$ and $Γ ⊢ a : A$ as they can be seen as reflexive case of the equality judgments. But we keep them for better readability.

In this chapter, we will consider structural type theories without modalities or type universes -- so that all type formers are well-behaved and simple.

#definition[
A _type theory_ is given by a set of rules for forming judgments inductively according to the schemas in @def_judgment.
]

We assume the readers to be familiar with the above notions of type theories.
Additionally, we assume readers to know some less formal terminologies, such as introduction rules, elimination rules, term formers, $β$-rules, $η$-laws, etc., which are common in type theory literature.

= Structures inside type theories

// Terminal object
#definition("Unit")[
We say a type theory has _unit type_ if it has a type $top$ where the following rules hold:

$ Γ ⊢ top #h(2em)
  Γ ⊢ ★ : top #h(2em)
  (Γ ⊢ a : top)/(Γ ⊢ a ≡ ★ : top)
  $
]

In any type theory, as long as we can assign $top$ and $★$ to an existing construction is considered a type theory with unit type.

#example[
The boolean type cannot be used to define a unit type, as it has two distinct terms, so the third rule does not hold.
]

// Initial object
#definition("Empty")[
We say a type theory has _empty type_ if it has a type $bot$ where the following rules hold:

$ Γ ⊢ mybot #h(2em)
  (Γ ⊢ a : mybot)/(Γ ⊢ "elim"(a) : A) #h(2em)
  (Γ, a:mybot ⊢ u: A)/(Γ, a: mybot ⊢ u ≡ "elim"(a) : A)
  $
]

// Cartesian product
#definition("Product")[
We say a type theory has _product type_ if it has a type former $A × B$ where the following rules hold:

TODO
]
