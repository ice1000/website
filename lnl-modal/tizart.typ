#import "@preview/ctheorems:1.1.2": *

#let project(title: "", subtitle: "", authors: (), size: 12pt, date: datetime.today(), body) = {
  // Set the document's basic properties.
  set document(author: authors.map(a => a.name), title: title)
  set page(numbering: "1", number-align: center)
  set text(font: (
    "Linux Libertine",
    "Source Han Serif SC",
    "Source Han Serif",
    // "Twitter Color Emoji Regular"
  ), lang: "en", size: size)
  // show math.equation: set text(font: (
  // ))
  // set par(first-line-indent: 1.8em)

  // Title row.
  align(center)[ #block(text(weight: 700, 1.75em, title)) ]
  if subtitle != "" {
    align(center)[ #block(text(1.25em, subtitle)) ]
  }
  align(center)[
    #v(1em, weak: true)
    #date.display("[month repr:short] [day], [year]")
  ]

  // Author information.
  pad(
    top: 0.5em,
    bottom: 0.5em,
    x: 2em,
    grid(
      columns: (1fr,) * calc.min(3, authors.len()),
      gutter: 1em,
      ..authors.map(author => align(center)[
        *#author.name* \
        #author.email
      ]),
    ),
  )

  // Main body.
  set par(justify: true)

  body
}

#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#let lemma = thmbox("lemma", "Lemma", fill: rgb("#eeffee"))
#let proof = thmproof("proof", "Proof")
