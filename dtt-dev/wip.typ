#import "config.typ": *
#show: dtt.with(title: "WIP")

// Cartesian coproduct
#definition("Sum")[
We say a type theory has _sum type_ if it has the following constructions:

+ $ (Γ⊢A #h(2em) Γ⊢B)/(Γ ⊢ A + B) $
  The _formation rule_,
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

#definition("Raw extensional equality")[
Given $Γ⊢a:A$ and $Γ⊢b:A$.
A _raw extensional equality_ consists of the following data:
+ A type $Γ⊢X$,
+ The equality reflection rule, namely
  $ (Γ⊢p:X)/(Γ⊢a≡b:A) $
]

Then, $a=_A b$ is an instance of such a raw extensional equality,
which can be characterized as follows:

#definition("Extensional equality")[
The extensional equality $a=_A b$ is a raw extensional equality such that
for every other raw extensional equality $X$, there exists a _unique_ term,
called the _reflexivity principle_:
+ $ Γ ⊢ h : a =_A b $
such that:
]
