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
#let elim = $sans("elim")$
#let refl = $sans("refl")$

#import "/book.typ": cross-link

#let dtt(title: "DTT", body) = {
  import "/book.typ": book-page
  show: thmrules.with(qed-symbol: $square$)
  show: book-page.with(title: title)

  show math.equation: it => {
    show "★": math.class.with("unary")
    show "∈": math.scripts
    show "⊢": math.scripts
    show "=": math.scripts
    it
  }

  body
}
