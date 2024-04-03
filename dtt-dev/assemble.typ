#let setup(title, authors) = {
  align(center)[ #block(text(weight: 700, 1.75em, title)) ]
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
}
#setup("Dependent Theory of Types", ((
  name: "Tesla Zhang",
  email: "teslaz@cmu.edu"
),))

#set heading(numbering: "1.")
#outline(depth: 2, indent: auto)
#import "intro.typ": intro-fulltext
#import "subst.typ": subst-fulltext
#import "struct-1.typ": struct-1-fulltext
#import "functor.typ": functor-fulltext
#import "struct-2.typ": struct-2-fulltext

= Introduction
#intro-fulltext
= Substitution Calculus
#subst-fulltext
= Structures I
#struct-1-fulltext
= Compilers
#functor-fulltext
= Structures, revisited
#struct-2-fulltext
