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

The paper @MemOIR observes that memory usages are usually _collections_, and proposes an IR with explicit representations of them.
Then, it proposes optimizations using the new abstraction.
We aim to extend this line of research to answer the following research questions:
- Can this IR represent Rust memory access patterns, as the authors claim it can?
- What comparable memory optimizations does the Rust compiler already perform?
- How effective are `MemOIR`'s proposed optimizations on Rust code?

The `MemOIR` paper claims their optimizations reduce both execution time and memory usage when applied before the standard LLVM optimization passes, on certain benchmarks.
Our project will be successful if we are able to replicate those results on the output of the Rust compiler.

== 75% Goal
- Give 10 Rust microbenchmarks and their `MemOIR` representations
- Analyze `MemOIR`-optimized benchmarks against `rustc`

== 100% Goal
- Reimplement the index live "range" analysis pass and the Dead Element Elimination pass from the paper

== 125% Goal
- Implement other transformations from the MemOIR paper (DFE, FE, RIE)
- Modify `rustc` to replace certain collection types with `MemOIR` operations
- Examine whether these optimizations are encountered in real-world Rust code

== 150% Goal
- Modify `rustc` to replace the Rust `struct` with `MemOIR` operations

= Plan of Attack and Schedule

We plan to do the work together by pair (triple?) coding. Joanna feels more comfortable with writing the optimization passes, so she might do disproportionately more of that.

#table(
  columns: 2,
  // stroke: (x, y) => {
  //   if (x == 0) {
  //     1pt
  //   } else {
  //     none
  //   }
  // },
  "until 10/27",
  "Get acquainted with the MemOIR implementation",
  "10/27-11/2",
  "Write three benchmarks in Rust, compile them to LLVM and manually insert MemOIR operations. Evaluate MemOIR optimization effects on the benchmarks.",
  "11/3-11/9",
  "Reimplement Dead Element Elimination based on MemOIR's implementation of live-range analysis. (Study for final exam)",
  "11/10-11/16",
  "Make more benchmarks and evaluate optimizations on them. Start reimplementing MemOIR live range analysis. (Take final exam)",
  "11/17-11/20",
  "Finish reimplemenation of MemOIR live range analysis. Write up the milestone report.",
  "11/21-11/27",
  "Compare our optimizations to the paper's, do the final write-up.",
  "11/28-12/3",
  "Make final presentation, practice final presentation twice."
)

= Milestone
We hope to have all of the code implemented for our 100% goal by the milestone deadline, and to spend the remaining time after the milestone preparing the paper and presentation.


= Literature Search

- Original paper: @MemOIR
- This cites many interesting papers on memory access and layout optimization, which we should read to compare in the final project. In particular @struct-splicing seems comparable.

= Resources Needed

We have everything we need.

= Getting started

We've read the paper and poked around in its references

#bibliography("papers.bib", style: "association-for-computing-machinery")
