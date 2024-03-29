#import "@preview/ctheorems:1.1.2": *

The purpose of this page is to test some random things.

#show: thmrules.with(qed-symbol: $square$)

#let definition = thmbox("definition", "Definition", inset: (x: 1.2em, top: 1em))

#let emsp = h(2em)
#definition("Heterogeneous Composition")[
$ (A:bb(I) → cal(U)_1 #emsp φ:bb(F) #emsp r, s : bb(I)
  #emsp u: (i:bb(I)) → "Partial"(φ ∨ i=r, A(i)))/(
  "com"^(r arrow.squiggly s)(u) : { A(s) | φ ∨ r=s ↦ u(s) }) $
]

== Harpoons

$ & "⇀-"β\
  & (Γ, x:A_1 ⊢ C_2:X_2 #h(2em) Γ ⊢ V_1 : A_1)/
    (Γ ⊢ "ap"(λ (x. C_2); V_1) ≡ [V_1 slash x]C_2 : X_2) $
$ & "⇀-"η\
  & (Γ ⊢ C : A_1 ⇀ X_2)/
    (Γ ⊢ λ (x. "ap"(C; x)) ≡ C : A_1 ⇀ X_2) $

== Coproducts

$ & "+-"β_1\
  & (Γ ⊢ V_1 : A_1 #h(2em) Γ, x:A_1 ⊢ C_1:X #h(2em) Γ, x:A_2 ⊢ C_2:X)/
    (Γ ⊢ "case" 1 · V_1 { x. C_1 | x. C_2 } ≡ [V_1 slash x]C_1 : X) $
$ & "+-"β_2\
  & (Γ ⊢ V_2 : A_2 #h(2em) Γ, x:A_1 ⊢ C_1:X #h(2em) Γ, x:A_2 ⊢ C_2:X)/
    (Γ ⊢ "case" 2 · V_2 { x. C_1 | x. C_2 } ≡ [V_2 slash x]C_2 : X) $
$ & "+-"η\
  & (Γ, x:A_1 + A_2 ⊢ C : X)/
    (Γ, x:A_1 + A_2 ⊢ "case" x {y. [1·y slash x]C | z. [2·z slash x]C} ≡ C : X) $
