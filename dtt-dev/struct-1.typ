#import "config.typ": *
#show: dtt.with(title: "Inside structures")

#let struct-1-fulltext = [
== Introduction

The goal of this chapter is to defined some simple strucures inside dependent type theories.

We assume readers to know some less formal terminologies, such as introduction rules, elimination rules, term formers, $β$-rules, $η$-laws, etc., which are common in type theory literature.

== Nullary connectives

// Terminal object
#definition("Unit")[
We say a type theory has a _unit type_ if it has the following constructions:

+ _Formation_: $ · ⊢ top $
+ _Introduction_: $ · ⊢ ★ : top $

such that the following rules hold:

+ The fact that the formation of unit type is preserved by substitution:
  $ Γ ⊢ top[σ] ≡ top $
+ The $η$-law: $ (Γ ⊢ a : top)/(Γ ⊢ a ≡ ★ : top) $
] <def_unit>

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

+ _Formation_: $ Γ ⊢ bot $
+ _Elimination_:
  $ (Γ, x:bot ⊢ u: A)/(Γ, x: bot ⊢ u ≡ elim_bot (x) : A)
  $

such that the following rules hold:

+ The fact that empty is preserved by substitution:
  $ Γ ⊢ bot[σ] ≡ bot $
+ The $η$-law:
  $ (Γ, x:bot ⊢ u: A)/(Γ, x: bot ⊢ u ≡ elim_bot (x) : A)
  $
]

Similarly we can state a theorem similar to @lem_subst_unit:
#lemma[The elimination of empty type is preserved by substitution:
$ (Δ,x:bot ⊢ a:A #h(2em) Γ ⊢ σ : Δ #h(2em) σ' := (σ,x slash x))/
  (Γ,x:bot ⊢ a[σ'] ≡ elim_bot (x) : A[σ']) $] <lem_subst_empty>
#proof[So by typing of the extended substitution object we know $ Γ,x:bot ⊢ σ' : (Δ,x:bot) $
therefore the substitution is well-typed and $ Γ,x:bot ⊢ a[σ'] : A[σ'] $
and by the $η$-law.]

#lemma[For every context extended by $bot$, there is a context isomorphism among each pair of them.

In other words, for all $Γ ⊢$ and $Δ ⊢$, we have a context isomorphism between $Γ, x:bot ⊢$ and $Δ, x:bot ⊢$.]
#proof[
The isomorphism $Γ, x:bot ⊢ σ : (Δ,x:bot)$ is given by a list of $elim_bot (x)$,
whose inverse is given alike.
]

Before proceeding further, we briefly describe the intended way to use these definitions.

There might be a type theory that does not directly define a unit type, but as long as it can provide the data and prove the equations needed by @def_unit, we can say it has a unit type, and may start using the rules of unit type in the type theory.

This is a form of _abstraction_, where we care only about how types are intended to be used, not how they are implemented,
and we use the abstracted rules which usually leads to lighter notations, shorter theorems and proofs, more efficient communications, and more general results.

== Product

// Cartesian product
#definition("Product")[
We say a type theory has _product types_ if it has the following constructions:

+  _Formation_:
  $ (Γ⊢A #h(2em) Γ⊢B)/(Γ ⊢ A × B) $
+ _Introduction_:
  $ (Γ ⊢ a:A #h(2em) Γ ⊢ b:B)/(Γ ⊢ ⟨a, b⟩ : A × B) $
+ _Elimination_:
  $ (Γ ⊢ p : A × B)/(Γ ⊢ p.1 : A)
    #h(2em)
    (Γ ⊢ p : A × B)/(Γ ⊢ p.2 : A)
  $

such that the following rules hold:

+ The fact that product is preserved by substitution:
  $ Γ ⊢ (A × B)[σ] ≡ A[σ] × B[σ] $
+  The fact that projections are preserved by substitution:
  $ Γ ⊢ p.1[σ] ≡ p[σ].1 : A \
    Γ ⊢ p.2[σ] ≡ p[σ].2 : B $
+ The $β$-rules:
  $ (Γ ⊢ a:A #h(2em) Γ ⊢ b:B)/(Γ ⊢ ⟨a,b⟩.1 ≡ a : A) \
    (Γ ⊢ a:A #h(2em) Γ ⊢ b:B)/(Γ ⊢ ⟨a,b⟩.2 ≡ b : B)
  $
+ The $η$-law:
  $ (Γ ⊢ p : A × B)/(Γ ⊢ p ≡ ⟨p.1, p.2⟩ : A × B)
  $
] <def_product>

#lemma("Product extensionality")[
The following rule is derivable:
$ (Γ ⊢ a.1 ≡ b.1 : A #h(2em) Γ ⊢ a.2 ≡ b.2 : B)/
  (Γ ⊢ a ≡ b : A × B)
  $
] <lem_product_ext>
#proof[By $η$-law, what we need to show is equivalently $⟨a.1, a.2⟩ ≡ ⟨b.1, b.2⟩$ and by congruence of equality.]

// Beck--Chevalley condition
#lemma[The introduction of product type is preserved by substitution:
$ Γ ⊢ ⟨a,b⟩[σ] ≡ ⟨a[σ], b[σ]⟩ : A[σ] × B[σ] $] <lem_subst_product>
#proof[
Let $u := ⟨a,b⟩[σ]$. By @lem_product_ext, the goal is equivalently $u.1 ≡ a[σ]$ and $u.2 ≡ b[σ]$.

Since projection is preserved by substitution, we have $(⟨a,b⟩[σ]).1 ≡ (⟨a,b⟩.1)[σ] ≡ a[σ]$, hence $u.1 ≡ a[σ]$, likewise $u.2 ≡ b[σ]$.
]

== Extensional equality

Before diving into more complicated dependently-typed structures, we first introduce a very simple type -- the extensional equality type.

// Equalizers
#definition("Equality")[
We say a type theory has _extensional equality type_ if it has the following constructions:

+ _Formation_:
  $ (Γ ⊢ A #h(2em) Γ ⊢ a:A #h(2em) Γ ⊢ b:A)/
    (Γ ⊢ a =_A b) $
+ _Introduction_:
  $ Γ ⊢ refl_a : a =_A a $

such that the following rules hold:

+ The fact that equality type is preserved by substitution:
  $ Γ ⊢ (a =_A b)[σ] ≡ (a[σ] =_(A[σ]) b[σ]) $
+ The _elimination rule_, also known as _equality reflection_:
  $ (Γ ⊢ p : a =_A b)/(Γ ⊢ a ≡ b : A) $
+ The $η$-law:
  $ Γ ⊢ (p ≡ refl_a) : (a =_A a) $
]

Before stating any properties of extensional equality, observe that in the $η$-law, we do not have a premise $Γ ⊢ p : a =_A b$.
This is because we have #cross-link("subst", reference: <def_presup>)[_presuppositions_], implying that this is already assumed when we _state_ the conclusion.

#lemma("Uniqueness")[The following judgment is _derivable_:
$ (Γ ⊢ p : a =_A b #h(2em) Γ ⊢ q : a =_A b)/
  (Γ ⊢ p ≡ q : a =_A b)
  $] <lem_uniqueness>
#proof[
By elimination of equality, we know $Γ ⊢ a ≡ b : A$, hence it suffice to show:
$ Γ ⊢ p ≡ q : a =_A a $
By $η$-law, both $p$ and $q$ are equal to $refl_a$.
]

#lemma[Having _extensional equality type_ and any closed term $· ⊢ a:A$ implies having a _unit type_.]
#proof[Let $top := (a =_A a)$ and $★ := refl_a$.]

== Conclusion

In this chapter, we have defined some simply-typed structures inside dependent type theories, including unit type, empty type, product type, and extensional equality type.

In the next chapter, we will seek to generalize some of these structures into a more general construction.
]
#struct-1-fulltext
