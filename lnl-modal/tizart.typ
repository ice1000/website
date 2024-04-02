#import "@preview/ctheorems:1.1.2": *

#let alpha = "33"
#let theorem = thmbox("theorem", "Theorem", breakable: true, fill: rgb("#eeffee" + alpha))
#let lemma = thmbox("lemma", "Lemma", breakable: true, fill: rgb("#eeffee" + alpha))
#let proof = thmproof("proof", "Proof")
