#import "/book.typ": book-page
#show: book-page.with(
  title: "Project Proposal",
  show-title: true,
  authors: (
    (name: "Joanna Boyland", email: "joannabo@andrew.cmu.edu", andrewid: "joannabo"),
    (name: "James Gallicchio", email: "jgallicc@cs.cmu.edu", andrewid: "jgallicc"),
    (name: "Tesla Zhang", email: "teslaz@cmu.edu", andrewid: "yinsenz")),
)
#set heading(numbering: "1.")

= Project Description

The paper @MemOIR observes that memory usage is dominated by _collections_, and proposes an IR with explicit representations of them. Programmers annotate their collections in order to tell MemOIR how to represent them. The paper introduces optimizations using the new abstraction, such as Dead Element Elimination.

We will reproduce their optimizations, without relying on the reference implementation (#link("https://github.com/arcana-lab/memoir")), as a pass in LLVM.
We will test this optimization on manually annotated C code,
and ideally eventually on Rust arrays and collections.

The `MemOIR` paper claims their optimizations reduce both execution time and memory usage when
applied before the standard LLVM optimization passes, on certain benchmarks.
Our project will be successful if we are able to replicate those results.

== 75% Goal

- Implement the collection IR in from the paper in LLVM
- Implement the index live "range" analysis pass and the Dead Element Elimination (DEE) pass from the paper for simple cases

Our benchmarks will be manually annotated, but we will write our own code to do the optimizations.

== 100% Goal

- Finish 75% goal
- Implement the index live "range" analysis pass and the DEE pass from the paper for general cases in C

== 125% Goal

There are several things we want to try, and we will decide which to pursue based on how the DEE optimization goes:

- Implement other optimizations from the MemOIR paper (Dead Field Elimination, Field Elision, Redundant Indirection Elimination)
- Integrate with `rustc` to hopefully generate annotations automatically since Rust restricts memory layout and usage patterns

= Plan of Attack and Schedule

We plan to do the work together by pair (triple?) coding.

#table(
  columns: (6em, 1fr),
  "10/28 - 11/2",
  "Implement the part of the collection IR we need from the MemOIR paper in LLVM, write some benchmarks, begin implementing live \"range\" analysis",
  "11/3 - 11/9",
  "Finish implementing the live \"range\" analysis.",
  "11/10 - 11/16 (final exam)",
  "Make more benchmarks and evaluate optimizations on them. Begin implementing the DEE pass.",
  "11/17 - 11/20",
  "Continue implementing the DEE pass, write up the milestone report.",
  "11/21 - 11/27",
  "Analyze the performance of our optimizations in comparison to the paper's, begin the chosen 125% goal(s).",
  "11/28 - 12/3",
  "Continue work on the chosen 125% option(s). Do final write-up and presentation."
)

= Milestone

We plan to have all of the code for DEE written by the milestone deadline, and be in the midst of testing/debugging, which we expect to take a significant amount of time.

= Literature Search 

- Original paper: @MemOIR
- This cites many interesting papers on memory access and layout optimization, which we should read to compare in the final project. In particular @struct-splicing seems comparable.

= Resources Needed

We have everything we need.

= Getting Started

We've read the paper and poked around in its references.

#bibliography("papers.bib", style: "association-for-computing-machinery")
