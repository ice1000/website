#import "@preview/ctheorems:1.1.2": *

#let alpha = "33"
#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee" + alpha))
#let lemma = thmbox("lemma", "Lemma", fill: rgb("#eeffee" + alpha))
#let definition = thmbox("definition", "Definition", fill: rgb("#DFF9FF" + alpha))
#let construction = thmbox("construction", "Construction", fill: rgb("#fff7f7" + alpha))
#let proof = thmproof("proof", "Proof")
#let example = thmbox("example", "Example").with(fill: rgb("#f7f7fd" + alpha))
#let mybot = box(sym.bot)

#let inl(x) = $sans("inl")(#x)$
#let inr(x) = $sans("inr")(#x)$
#let wk(x) = $sans("wk")(#x)$
