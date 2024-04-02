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

So, we _weaken_ $b$ to be:
$ Γ,A,B[π_A] ⊢ b[π_B[π_A]] :B[π_(B[π_A]);π_A] $
And turn $a$ into a substitution:
$ Γ,B,A[π_B] ⊢ (id_(Γ,B),a[π_(A[π_B])]) : Γ,B,A[π_B] $
Let's denote $a' := id_(Γ,B),a[π_(A[π_B])]$.
Then I apply the substitution. Let $σ := ex(B,A);a';π_B[π_A]$, then:
$ b[σ] : B[σ;π_A] $
by definition of projections, we know that
$ σ;π_A = ex(B,A);a';π_(B[π_A]);π_A ≡ id_(Γ,A) $
therefore

We assemble the above into the following definition:

#definition[In a type theory and a context $Γ$,
we say two types $Γ⊢A$, $Γ⊢B$ to be _equivalent_ if we have the following terms:

$ Γ,x:A ⊢ b:B[π_A] #h(3em) Γ,x:B ⊢ a:A[π_B] $

such that the following equalities are derivable:

TODO
// $ Γ,x:A ⊢ a[b slash x] ≡ x : A[π_A] $
]

