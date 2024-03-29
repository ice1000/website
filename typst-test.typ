#import "@preview/ctheorems:1.1.2": *

#show: thmrules.with(qed-symbol: $square$)

#let definition = thmbox("definition", "Definition", inset: (x: 1.2em, top: 1em))

#definition(name: "Heterogeneous Composition")[
$ (A:bb(I) → cal(U)_1 #h(2em) φ:bb(F) #h(2em) u: (i:bb(I)) → "Partial"(φ ∨ i=0, A(i)))/("com"(u) : { A(1) | φ ↦ u(1) }) $
]
