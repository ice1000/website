#import "/book.typ": book-page

#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/cetz:0.4.2": canvas, draw
#import "@preview/cetz-plot:0.1.3": chart

#show: book-page.with(
  title: "Dead Element Elimination on SSA Collections",
  authors: (
    (name: "Joanna Boyland", email: "joannabo@andrew.cmu.edu", andrewid: "joannabo"),
    (name: "James Gallicchio", email: "jgallicc@cs.cmu.edu", andrewid: "jgallicc"),
    (name: "Tesla Zhang", email: "teslaz@cmu.edu", andrewid: "yinsenz")),
  show-title: true,
)
#set heading(numbering: "1.")

This document is the project for the course
Optimizing Compilers for Modern (15-745).

= Introduction

#set enum(numbering: "(a)")
+ The Problem: Sometimes a program writes to a memory location that is not later accessed, which means the write is dead code.
  If the memory location is a scalar, it's easy to detect when it's not used.
  However, when we write to a data sequence, such as a sequential collection or map,
  it's much harder to detect which writes do not affect the output.
  The compilation process generally treats collection operations as normal function calls,
  hiding the optimization opportunity.
// What problem are you solving (or what opportunity that you are attempting to exploit)?
+ Our Approach:
  We introduce a distinguished set of sequence operations in the program
  and run an analysis pass to find the "live range" of each sequence:
  that is, what range of indices in the sequence might be read from in the future.
  Then, we run a function pass to add runtime checks so that we only write to a sequence when we write within its live range.
  To make this feasible to do in LLVM, we build a set of sequence APIs and write the sample code using these APIs,
  and recognize them in the pass.
// What is your approach to either solving this problem or exploiting this opportunity? (Don’t go into a huge amount of detail yet—that will come in the next section; just give a thumbnail sketch at this point.)
+ Related Work: We are working from the paper MemOIR @MemOIR, re-implementing their live-range analysis and dead-element elimination passes.
  There is a provided implementation, but it only handles read, write, copy, and ranged copy for sequences.
  The scalar range information is collected using another project called `noelle`.
// What have others done in the past that is related to your approach?
+ Contributions: We assume the programs are using immutable sequences by designing the APIs in this way.
  Then, we analyze the scalar variables used as indices using built-in LLVM passes (`LazyValueInfo` and `ScalarEvolution`)
  in order to generate the integer range the variables could have as values.
  Next, we build up a graph of constraints between sequences and indices:
  if a certain range of indices in a sequence might be used later, that's called the live range of the sequence,
  and there are dependencies between the live ranges of sequences and the ranges of index variables.
  We solve the constraints to get the live index ranges of every sequence in a function.
  Then, at each write, we insert a branch so that the write only occurs if the index we're writing to is in the live range.
  Lastly, we have a separate pass that exits out of SSA form,
  converting immutable sequence operations to mutable operations, to avoid the excessive copying of immutable collection APIs.
// #text(red)[IDK what to say that isn't already/will be said]
// What are the key technical contributions of your project?


=  Implementation Details
// Here is where you go into detail regarding how you solved your technical problem. This can be multiple sections, and you need a more descriptive name for the section(s) than this. If your design evolved over time, please explain that evolution (not just the final design), and the reasons why it changed.
In this section we discuss the implementation, and make comparison with the provided implementation of MemOIR.

== The Intermediate Representation
The provided implementation has its own IR builder and instruction types. We use LLVM function calls to imitate special instructions, and implement the instructions as library functions (see `imm.h` and `mut.h`).

We implemented two sets of collection APIs, including immutable (`imm.h`):

#block(inset: 1em)[```c
typedef struct ImmSeqData *ImmSeq;

ImmSeq  imm_new(int length);
int     imm_size(ImmSeq seq);
ImmSeq  imm_copy_range(ImmSeq seq, int index, int length);
ImmSeq  imm_copy(ImmSeq seq);
float   imm_read(ImmSeq seq, int index);
ImmSeq  imm_write(ImmSeq seq, int index, float value);
ImmSeq  imm_insert(ImmSeq seq, int index, float value);
```]

And mutable (`mut.h`):

#block(inset: 1em)[```c
typedef struct MutSeqData* MutSeq;

MutSeq mut_new(int length);
MutSeq mut_copy_range(MutSeq seq, int index, int length);
MutSeq mut_copy(MutSeq seq);
float mut_read(MutSeq seq, int index);
void mut_write(MutSeq seq, int index, float value);
void mut_insert(MutSeq seq, int index, float value);
```]

In the immutable API, all mutations are done by making a new copy and assign to the old variables.
For example, instead of writing to an array `s0` via `s0[i]=v`, we write to it by creating a new sequence `s1` from the old sequence `s0` using our specialized function `imm_write`, as in `s1 = imm_write(s0,i,v)`, followed by setting `s0=s1`.
This means that when the built-in LLVM passes converts our program into SSA form, it adds in φ functions automatically. And due to the nature of immutable APIs, the _elements_ are also in SSA: not only variables have unique _reaching definition_, the `i`-th element of each sequence also have unique _reaching initialization_. The idea of sequence SSA goes back to @ArraySSA.

The mutable APIs are more like standard sequence APIs, like `mut_write(m, i, a)` replace the `i`-th element of `m` with `a`, instead of creating a new copy. After the optimization, we will convert immutable calls to mutable calls, and insert a copy if the original is still live.

The immutable API is for analysis, not running. The mutable API is meant to be executed. We do _implement_ the immutable APIs so we run the code and compare output for correctness.

== Scalar Range Analysis
Corresponding source files: `value_range.cpp` and `dee_pass.cpp`

We iterate through all the scalars that are used to index into sequences, and find which (integer) ranges the scalars could lie in. 

The provided implementation uses a project called `noelle` to do scalar range analysis.

We use the built-in LLVM passes `LazyValueInfo` and `ScalarEvolution` for each scalar. The former gives good upper bounds and the latter gives good lower bounds, so we intersect them and get a very respectable constant range (the bounds are exact in simple cases).

== Building the Constraint Graph

Corresponding source files: `live_range_graph.cpp` and `dee_pass.cpp`.

We have a graph data structure where the vertices are sequences or index variables and there are directed multi-edges labelled with constraints. Constraints are functions from live ranges of the first vertex to the second.

The provided implementation encapsulated an open source C++ graph library as a directed graph. We reused their directed graph implementation and modified it to allow multi-edges, which we need for insert.

We iterate through all calls to our specialized sequence access functions and add in constraints, depending on the scalar range analysis and on what type of call it is. The provided implementation supports read, write, new, copy, and ranged copy. This is also why they didn't need multi-edges, because these operations operate _linearly_ on constraints, say, each constraint on the output will become one constraint on the input. We extended their set of supported operations with insertion, which for each constraint on the output, it produces two constraints on the input because insert splits the original sequence at the point of insertion.

The handling of insert is part of the 125% goal; it required updating the data structure to allow multi-edges and was not implemented by the original paper.

== Solving the Constraint Graph

Corresponding source file: `dee_pass.cpp`.

Essentially, we need to find a fixed point of the functions in this graph. Instead of solving it via an iterative dataflow framework, we calculate the condensation graph of the constraint graph, where each node of the condensation graph represents a strongly connected component of the original constraint graph. Each pair of nodes thus has no interdependencies between them: we can only have one direction of dependencies. So we can work through the _condensation_ graph in topological order and resolve the each node all at once before proceeding to the next node.

This part is essentially the same as MemOIR's provided implementation, except that we fold the multi-edges during constraint propagation.

== Dead Element Elimination

Corresponding source file: `dee_pass.cpp`.
This is the 75% goal.

With the live range constraint graph, we insert runtime checks at every write and insert operation so that we only modify index `i` of sequence `s` if `i` is in the live range of `s`.
Since the scalar ranges we generate are constant, some of the live ranges we generate for our sequences are too. So, if we run other built-in optimization passes such as constant propagation and path-sensitive dead code elimination, many of our runtime checks can be resolved at compile time, eliminating the elements that are dead.

We did not refer to the provided implementation, so we do not know how they did this.

== Exit SSA
Corresponding source file: `ssa_exit_pass.cpp`.
This is the 100% goal.

In a separate pass, for each immutable copying operation `%new = call imm_*(%old, ...)`, we investigate all other uses of `%old`. If no other uses of `%old` are reachable from `%new`, i.e `%old` is never accessed again, we replace the copying operation with a corresponding mutable operation. This avoids copying the entire immutable collection, which is costly.

We did not refer to the provided implementation, so we do not know how MemOIR implements this. But the provided implementation also implement this as a separate pass.

= Experiments

We manually wrote a number of tests that would exercise
the collection dead element elimination.
Running the test suite produces the data presented in the Evaluation section.

== Setup
The project is built with CMake, and the testing is executed using the script `compile_test.sh`. The makefile generated by CMake will have a `runtest` option to run `compile_test.sh` directly.

The project has been built and tested with LLVM 20.

The recommended way to use CMake is via the following commands:

```sh
mkdir build && cd build
cmake ..
make runtest # or just make to compile
```

== Evaluation

We evaluated our optimizations for multiple properties.
First, we tested for correctness,
ensuring the optimizations did not alter the program result.
Second, we tested that we were successfully eliminating copying operations
in the SSA exit pass.
Third, we tested that we were successfully eliminating
operations on dead elements.

See @table for a summarized view of our evaluation data.
In "no DEE" runs, the test was compiled to an executable without applying DEE,
but still exiting SSA and switching to mutable collection operations.
In the "DEE" runs, we compiled with the same optimization passes,
but now inserting the DEE pass as well.

#show table.cell.where(y: 0): strong
#set table(
  stroke: (x, y) => if y == 0 {
    (bottom: 1.5pt + black)
  },
  align: (x, y) => (
    if x > 0 { center }
    else { left }
  )
)

#show figure.caption: body => { set par(leading: 0.2em); body }
#figure(caption: [
  Operation counts from selected test cases.
  In all tests, exiting SSA successfully removes _all_ collection copying.
], [
#table(
  columns: (auto, auto, 1fr, 1fr, 1fr, 1fr),
  align: (left, left, right, right, right, right),
  table.header([Test Case], [Opt?], [`copy`], [`read`], [`write`], [`insert`]),
  table.cell(rowspan: 2, align: horizon)[`scalarrangetest.c`],
    [no DEE], [0], [    20], [  6000], [     0],
    [DEE   ], [0], [    20], [     6], [     0],
  table.hline(stroke: 0.5pt),
  table.cell(rowspan: 2, align: horizon)[`insert_tons...`],
    [no DEE], [0], [    10], [     0], [ 10000],
    [DEE   ], [0], [    10], [     0], [    10],
  table.hline(stroke: 0.5pt),
  table.cell(rowspan: 3, align: horizon)[`write_tons...`],
    [no DEE], [0], [100100], [110000], [     0],
    [DEE   ], [0], [  1100], [ 11000], [     0],
    [DEE ×2], [0], [  1100], [  1100], [     0],
  table.hline(stroke: 0.5pt),
  table.cell(rowspan: 2, align: horizon)[`matmul.c`],
    [no DEE], [0], [  4010], [   500], [     0],
    [DEE   ], [0], [  4010], [   500], [     0],
)
]) <table>


We will briefly explain what each test does,
and how our optimization can eliminate operations in the test.


=== `scalarrangetest.c`

This is the simplest test case where DEE should have an impact.
The test case writes to a large sequential collection,
and then does not read from most of its indices.
This is the simplest case where DEE should work,
and we successfully identify the dead ranges of this array
and insert guards to avoid writing to those ranges.



=== `insert_tons_of_memory_we_dont_use.c`

This test case is similar to the prior,
but rather than writing to a large array,
we perform inserts into that array.
Unlike `write`s, `insert`s change the size of the array,
and move any elements that come after the insert to a new index.
This requires more complexity in the implementation to infer
correct live ranges.

Again, we successfully identify that most of the collection is dead,
and optimize away most of the insertions.

=== `write_tons_of_memory_we_dont_use.c`

This is an interesting test case, because the DEE optimization
enables other optimizations to further improve the code.
In this test case, we write data to a large sequential array,
and then apply a transformation to each element
(in this test we square each element).
We ultimately only read from a small part of the transformed array,
so intuitively both the transformed array and the original array
are mostly dead.

On the first DEE pass, we identify that the array after transformation is mostly dead,
and insert a guard to only write the portion of the array that will be read.
However, for the first pass, the array _before_ transformation is considered all alive,
because the transformation step of course reads every element of the original array.

After inserting a guard on the transformation write,
we can apply a series of standard optimisation passes
(`sink` is the most important one)
to reduce how much of the original array we read.
Then, we can apply DEE for a second time to eliminate dead writes in the original array.
This is why, in the table, the number of writes is reduced after both the first and second DEE passes.

=== `matmul.c`

This was one of the first test cases we wrote.
It does a standard matrix multiplication of some large matrices,
but then only uses the first row of the resulting matrix.
In theory, only the first row of the first input matrix would be live,
and the rest of the matrix dead.
However, we were not able to get our DEE pass to infer tight enough bounds
on the index expression to optimize it.

This test seems very feasible for our implementation to handle,
but demonstrates the relative fragility of this optimization;
when we cannot infer good bounds on the scalar quantities in the code,
we are unable to identify any optimization opportunities.


#let data2 = (
  ([`scalarrangetest.c`],
    1, 1,
    1, 6/6000,
    0, 0,
    ),
  ([`insert_tons...`],
    1, 1,
    0, 0,
    1, 0.01
    ),
  ([`write_tons...` (DEE once)],
    1, 1100/100100,
    1, 11000/110000,
    0, 0,
    ),
  ([`write_tons...` (DEE twice)],
    1, 1100/100100,
    1, 1100/110000,
    0, 0,
    ),
  ([`matmul.c`],
    1, 1,
    1, 1,
    0, 0
  ),
)
// apparently putting 100100, 1, 0, 10 in the same diagram makes sense
// shall we logarithm?

#figure(caption: [
  A visualization of the test case evaluation data from @table.
  The saturated colors are before DEE, the pale colors are after.
  We've also normalized the before/after DEE comparisons.
], canvas({
  draw.set-style(legend: (fill: white), barchart: (bar-width: .8, cluster-gap: 0))
  chart.barchart(
    mode: "clustered",
    size: (6, auto),
    label-key: 0,
    value-key: (..range(1, 7)),
    x-min: -0.05, x-max: 1.05,
    x-tick-step: 1,
    x-format: (x => [#(100*x)%]),
    data2,
    labels: ([reads (no DEE)], [reads (DEE)], [writes (no DEE)], [writes (DEE)], [inserts (no DEE)], [inserts (DEE)]),
    bar-style: idx => {
      let color = (red,red.lighten(60%),blue,blue.lighten(65%),green,green.lighten(60%)).at(idx);
      (fill: color)
    },
    //legend: "",
)
})) <barchart>

= Surprises and Lessons Learned: 
// Were any of your results surprising or counter-intuitive? If so, what did you learn from those surprises? What did you learn from this experience in general?
The results were what we expected, because the optimizations triggered were highly predictable. However, we were surprised that even with just the constant ranges from the LLVM built-in scalar range analysis passes, we can do a lot of optimizations. Anything beyond constant ranges requires significantly more complicated implementation, without necessarily increasing the likelihood of compile-time eliminations.

During this experience, we also learned how to implement non-iterative algorithms
for solving dataflow problems, namely via the condensation graph.


=  Conclusions and Future Work: 
//Present the technical conclusions of your work (i.e. things that you now know that you did not know at the beginning of this study), and suggest how someone might build upon your work in the future (if that makes sense).
// We did not previously know the  of finding fixed points, so 
 
We did not implement everything from the paper (nor did they), so someone could re-implement the rest using our setup or MemOIR's.

In future work, one could potentially try to analyze liveness as more general subsets rather than ranges. For example, if a sequence is only used at the very beginning and the very end, the live range would still be considered to be the whole sequence. Or, if the sequence is only used at its even indices, a live range analysis would not be able to optimize away all writes to odd indices. 
// maybe unimportant rant: The MemOIR paper claims to use a lattice where expression trees are comparable via the subtree relation. This doesn't seem to be compatible with the poset relation used in our constraints (we say that a function of the live range of some `s1` is _contained_ in the live range of some `s0`). Something we could do is add in more detail such that 

= Distribution of Total Credit: 

We all worked very hard to make this happen, so the credit should be distributed evenly.

#bibliography("papers.bib", style: "association-for-computing-machinery")
