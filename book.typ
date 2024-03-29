#import "@preview/book:0.2.4": *

#show: book

#book-meta(
  // title: "Tesla Zhang",
  repository: "https://github.com/ice1000/ice1000.github.io",
  authors: ("Tesla Zhang",),
  language: "en",
  summary: [
    #prefix-chapter("index.typ")[About]
  ]
)

// re-export page template
#import "/templates/page.typ": project
#let book-page = project
