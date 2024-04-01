#import "config.typ": *
#import "/book.typ": book-page
#show: thmrules.with(qed-symbol: $square$)
#show: book-page.with(title: "Inside structures")

#show math.equation: it => {
  show "★": math.class.with("unary")
  it
}

= Introduction

The goal of this chapter is to defined strucures inside dependent type theories.

We assume readers to know some less formal terminologies, such as introduction rules, elimination rules, term formers, $β$-rules, $η$-laws, etc., which are common in type theory literature.

= Structures inside type theories

// Terminal object
#definition("Unit")[
We say a type theory has _unit type_ if it has a type $top$ where the following rules hold:

+ $Γ ⊢ top$ the _formation rule_,
+ $Γ ⊢ top[σ] ≡ top$ the fact that unit is preserved nu substitution action,
+ $Γ ⊢ ★ : top$ the _introduction rule_,
+ $ (Γ ⊢ a : top)/(Γ ⊢ a ≡ ★ : top)
  $
  The $η$-law.
]

#lemma[The introduction of unit type is preserved by substitution:
$ Γ ⊢ ★[σ] ≡ ★ : top $] <lem_subst_unit>
#proof[Because $Γ ⊢ ★[σ] : top$, and by the $η$-law.]

In any type theory, as long as we can assign $top$ and $★$ to an existing construction, we consider this type theory to have unit type.

#example[
The boolean type cannot be used to define a unit type, as it has two distinct terms, so the $η$-law does not hold.
]
#lemma[
The projection of a unit type, $Γ,x:top ⊢ π_top : Γ$ is a context isomorphism.]
#proof[The inverse is given by the identity substitution extended with $★$, the introduction of $top$.]
In fact, this can be used alternatively to define a unit type.

// Initial object
#definition("Empty")[
We say a type theory has _empty type_ if it has a type $bot$ where the following rules hold:

+ $Γ ⊢ mybot$ the _formation rule_,
+ $Γ ⊢ mybot[σ] ≡ mybot$ the fact that empty is preserved nu substitution action,
+ $ (Γ ⊢ a : mybot)/(Γ ⊢ elim_mybot (a) : A)
  $
  The _elimination rule_,
+ $ (Γ, x:mybot ⊢ u: A)/(Γ, x: mybot ⊢ u ≡ elim_mybot (x) : A)
  $
  The $η$-law.
]

Similarly we can state a theorem similar to @lem_subst_unit:
#lemma[The elimination of empty type is preserved by substitution:
$ (Δ,x:mybot ⊢ a:A #h(2em) Γ ⊢ σ : Δ #h(2em) σ' := (σ,x slash x))/
  (Γ,x:mybot ⊢ a[σ'] ≡ elim_mybot (x) : A[σ']) $] <lem_subst_empty>
#proof[So by typing of the extended substitution object we know $ Γ,x:mybot ⊢ σ' : (Δ,x:mybot) $
therefore the substitution is well-typed and $ Γ,x:mybot ⊢ a[σ'] : A[σ'] $
and by the $η$-law.]

#lemma[For every context extended by $mybot$, there is a context isomorphism among each pair of them.

In other words, for all $Γ ⊢$ and $Δ ⊢$, we have a context isomorphism between $Γ, x:mybot ⊢$ and $Δ, x:mybot ⊢$.]

// Cartesian product
#definition("Product")[
We say a type theory has _product type_ if it has a type former $A × B$ where the following rules hold:

$ Γ ⊢ A × B #h(2em)
  (Γ ⊢ a:A #h(2em) Γ ⊢ b:B)/(Γ ⊢ ⟨a, b⟩ : A × B) \
  (Γ ⊢ p : A × B)/(Γ ⊢ p.1 : A)
  #h(2em)
  (Γ ⊢ a:A #h(2em) Γ ⊢ b:B)/(Γ ⊢ ⟨a,b⟩.1 ≡ a : A) \
  (Γ ⊢ p : A × B)/(Γ ⊢ p.2 : A)
  #h(2em)
  (Γ ⊢ a:A #h(2em) Γ ⊢ b:B)/(Γ ⊢ ⟨a,b⟩.2 ≡ b : B) \
  (Γ ⊢ p : A × B)/(Γ ⊢ p ≡ ⟨p.1, p.2⟩ : A × B)
  $
]

// Cartesian coproduct
#definition("Sum")[
We say a type theory has _sum type_ if it has a type former $A + B$ where the following rules hold:

$ Γ ⊢ A + B #h(2em)
  (Γ ⊢ a:A)/(Γ ⊢ inl(a) : A + B) #h(2em)
  (Γ ⊢ b:B)/(Γ ⊢ inr(b) : A + B) \
  (Γ ⊢ s : A + B #h(2em) Γ, x:A ⊢ u : C #h(2em) Γ, y:B ⊢ v : C)/(Γ ⊢ elim_+(s, x. u, y. v) : C) \
  (Γ ⊢ a:A)/(Γ ⊢ elim_+(inl(a), x. u, y. v) ≡ u[a slash x] : C) \
  (Γ ⊢ b:B)/(Γ ⊢ elim_+(inr(b), x. u, y. v) ≡ v[b slash y] : C)
  $
  TODO
]
