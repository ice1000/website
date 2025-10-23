#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#let project(title: "", subtitle: "", authors: (), size: 12pt, date: datetime.today(), body) = {
  // Set the document's basic properties.
  set document(author: authors.map(a => a.name), title: title)
  set page(numbering: "1", number-align: center)
  set text(font: (
    "Linux Libertine",
    // "Twitter Color Emoji Regular"
  ), lang: "en", size: size)

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
        #author.email \
        #author.andrewid
      ]),
    ),
  )

  // Main body.
  set par(justify: true)

  body
}

#show: project.with(
  title: "Representing Rust Collections in an SSA Form",
  authors: (
    (name: "Joanna Boyland", email: "joannabo@andrew.cmu.edu", andrewid: "joannabo"),
    (name: "James Gallicchio", email: "jgallicc@cs.cmu.edu", andrewid: "jgallicc"),
    (name: "Tesla Zhang", email: "teslaz@cmu.edu", andrewid: "yinsenz")),
  date: datetime.today()
)

#align(center)[15-745 Optimizing Compilers]

This is a stub @DataSSA.

#bibliography("papers.bib", style: "association-for-computing-machinery")

