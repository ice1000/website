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
    - #chapter("lnl-modal/report.typ")[LNL Cxl Modal Logic],
    - #chapter("memoir/report.typ")[Rust Data in SSA],
      - #chapter("memoir/proposal.typ")[Project Proposal],
    // #chapter("dtt-dev/assemble.typ")[Dependent Theory of Types],
    = Miscellaneous
    - #chapter("resume.typ")[Industry Resume],
    - #chapter("typst-test.typ")[Typesetting Experiments],
  ]
)

// re-export page template
#import "/templates/page.typ": project
#let book-page = project
