#import "@preview/shiroa:0.2.3": *
#show: book

#book-meta(
  // title: "Tesla Zhang",
  repository: "https://github.com/ice1000/ice1000.github.io",
  authors: ("Tesla Zhang",),
  language: "en",
  summary: [
    #prefix-chapter("index.typ")[About],
    = Academic Writing
    #prefix-chapter("lnl-modal/report.typ")[LNL Cxl Modal Logic],
    #prefix-chapter("mem-ssa/report.typ")[SSA Memory],
    // #prefix-chapter("dtt-dev/assemble.typ")[Dependent Theory of Types],
    = Miscellaneous
    #prefix-chapter("resume.typ")[Industry Resume],
    #prefix-chapter("typst-test.typ")[Typesetting Experiments],
  ]
)

// re-export page template
#import "/templates/page.typ": project
#let book-page = project
