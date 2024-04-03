#import "@preview/ctheorems:1.1.2": *

#let alpha = "33"
#let theorem = thmbox("theorem", "Theorem", breakable: true, fill: rgb("#eeffee" + alpha))
#let lemma = thmbox("lemma", "Lemma", breakable: true, fill: rgb("#eeffee" + alpha))
#let corollary = thmbox("corollary", "Corollary", breakable: true, fill: rgb("#eeffee" + alpha))
#let definition = thmbox("definition", "Definition", breakable: true, fill: rgb("#DFF9FF" + alpha))
#let construction = thmbox("construction", "Construction", breakable: true, fill: rgb("#fff7f7" + alpha))
#let example = thmbox("example", "Example", breakable: true, fill: rgb("#f7f7fd" + alpha))
#let lesson = thmbox("lesson", "Lesson", breakable: true, fill: rgb("#FFCCCB" + alpha))
#let proof = thmproof("proof", "Proof")

#let mybot = box(sym.bot)
#let inl(x) = $sans("inl")(#x)$
#let inr(x) = $sans("inr")(#x)$
#let wk(x) = $sans("wk")(#x)$
#let elim = $sans("elim")$
#let refl = $sans("refl")$
#let ex(A,B) = $sans("ex")_(#A, #B)$

#import "/book.typ": cross-link as lib-cross-link

#let cross-link(path, reference: none, content) = lib-cross-link("/dtt-dev/" + path + ".typ", reference: reference, content)

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
