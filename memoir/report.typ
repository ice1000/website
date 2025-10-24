#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#import "/book.typ": book-page
#show: book-page.with(
  title: "Representing Rust Collections in an SSA Form",
  show-title: true,
  authors: (
    (name: "Joanna Boyland", email: "joannabo@andrew.cmu.edu", andrewid: "joannabo"),
    (name: "James Gallicchio", email: "jgallicc@cs.cmu.edu", andrewid: "jgallicc"),
    (name: "Tesla Zhang", email: "teslaz@cmu.edu", andrewid: "yinsenz")),
)
#set heading(numbering: "1.")

#align(center)[15-745 Optimizing Compilers]

Links:

- #link("proposal")[Project Proposal]
