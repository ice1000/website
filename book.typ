#import "@preview/book:0.2.4": *
#show: book

#book-meta(
  // title: "Tesla Zhang",
  repository: "https://github.com/ice1000/ice1000.github.io",
  authors: ("Tesla Zhang",),
  language: "en",
  summary: [
    #prefix-chapter("index.typ")[About],
    #prefix-chapter("lnl-modal/report.typ")[LNL Cxl Modal Logic],
    = Dependent Theory of Types
    #chapter("dtt-dev/limits.typ")[Finite Limits],
    = Miscellaneous
    #prefix-chapter("resume.typ")[Industry Resume],
    #prefix-chapter("typst-test.typ")[Typesetting Experiments],
  ]
)

// re-export page template
#import "/templates/page.typ": project
#let book-page = project
