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
We say a type theory has _unit type_ if it has the following constructions:

+ $Γ ⊢ top$ the _formation rule_,
+ $Γ ⊢ ★ : top$ the _introduction rule_;

such that the following rules are derivable:

+ $Γ ⊢ top[σ] ≡ top$ the fact that unit is preserved by substitution action,
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
#proof[The inverse is given by the identity substitution extended with the introduction of $top$: $ Γ ⊢ (id_Γ,★) : (Γ,x:top) $]
In fact, this can be used alternatively to define a unit type.

// Initial object
#definition("Empty")[
We say a type theory has _empty type_ if it has the following constructions:

+ $Γ ⊢ mybot$ the _formation rule_,
+ $ (Γ ⊢ a : mybot)/(Γ ⊢ elim_mybot (a) : A)
  $
  The _elimination rule_;

such that the following rules are derivable:

+ $Γ ⊢ mybot[σ] ≡ mybot$ the fact that empty is preserved by substitution action,
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
#proof[
The isomorphism $Γ, x:mybot ⊢ σ : (Δ,x:mybot)$ is given by a list of $elim_mybot (x)$,
whose inverse is given alike.
]

// Cartesian product
#definition("Product")[
We say a type theory has _product type_ if it has the following constructions:

+ $Γ ⊢ A × B$ the _formation rule_,
+ $ (Γ ⊢ a:A #h(2em) Γ ⊢ b:B)/(Γ ⊢ ⟨a, b⟩ : A × B)
  $
  The _introduction rule_,
+ $ (Γ ⊢ p : A × B)/(Γ ⊢ p.1 : A)
    #h(2em)
    (Γ ⊢ p : A × B)/(Γ ⊢ p.2 : A)
  $
  The _elimination rules_;

such that the following rules are derivable:

+ $Γ ⊢ (A × B)[σ] ≡ A[σ] × B[σ]$ the fact that product is preserved by substitution action,
+ $ (Γ ⊢ a:A #h(2em) Γ ⊢ b:B)/(Γ ⊢ ⟨a,b⟩.1 ≡ a : A) \
    (Γ ⊢ a:A #h(2em) Γ ⊢ b:B)/(Γ ⊢ ⟨a,b⟩.2 ≡ b : B)
  $
  The $β$-rules,
+ $ (Γ ⊢ p : A × B)/(Γ ⊢ p ≡ ⟨p.1, p.2⟩ : A × B)
  $
  The $η$-law.
]

// Cartesian coproduct
#definition("Sum")[
We say a type theory has _sum type_ if it has the following constructions:

+ $Γ ⊢ A + B$ the _formation rule_,
+ $ (Γ ⊢ a:A)/(Γ ⊢ inl(a) : A + B) \ (Γ ⊢ b:B)/(Γ ⊢ inr(b) : A + B)
  $
  The _introduction rules_,
+ $ (Γ ⊢ s : A + B \ Γ, x:A ⊢ u : C #h(2em) Γ, y:B ⊢ v : C)/
    (Γ ⊢ elim_+(s, x. u, y. v) : C)
  $
  The _elimination rule_;

such that the following rules are derivable:

+ $Γ ⊢ (A + B)[σ] ≡ A[σ] + B[σ]$ the fact that sum is preserved by substitution action,
+ $ (Γ ⊢ a:A)/(Γ ⊢ elim_+(inl(a), x. u, y. v) ≡ u[a slash x] : C) \
    (Γ ⊢ b:B)/(Γ ⊢ elim_+(inr(b), x. u, y. v) ≡ v[b slash y] : C)
    $
  The $β$-rules,
+ $ (Γ, x:A+B ⊢ u : C \
     u_1 := u[inl(y) slash x] #h(2em)
     u_2 := u[inr(y) slash x]
    )/
    (Γ, x:A+B ⊢ u ≡ elim_+(x, y. u_1, y. u_2) : C)
  $
  The $η$-law.
]
