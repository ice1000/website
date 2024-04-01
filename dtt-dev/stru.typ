#import "config.typ": *
#import "/book.typ": book-page
#show: thmrules.with(qed-symbol: $square$)
#show: book-page.with(title: "Inside structures")

We assume readers to know some less formal terminologies, such as introduction rules, elimination rules, term formers, $β$-rules, $η$-laws, etc., which are common in type theory literature.

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
