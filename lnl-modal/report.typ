#import "tizart.typ": *
#import "prooftree.typ": prooftree, axiom, rule
#show: thmrules.with(qed-symbol: $square$)

#import "/book.typ": book-page
#show: book-page.with(
  title: "Linear/Non-Linear Contextual Modal Logic",
  show-title: true,
  authors: ((
    name: "Wojciech Nawrocki",
    email: "wjnawrocki@cmu.edu"
  ), (
    name: "Tesla Zhang",
    email: "teslaz@cmu.edu"
  ))
)
#set heading(numbering: "1.")

#show math.equation: it => {
  show sym.arrow.t: math.class.with("unary")
  show sym.arrow.b: math.class.with("unary")
  it
}

// Good box
#let gbox(content) = box(stroke: black, inset: 5pt, baseline: 4pt, content)

This document is the miniproject project for the course
Substructural Logics (15-836, #link("https://www.cs.cmu.edu/~fp/courses/15836-f23")).

/* = Project description

This section is adapted from the miniproject description from the course
Substructural Logics (15-836, #link("https://www.cs.cmu.edu/~fp/courses/15836-f23")).

Originally, contextual modal type theory @08nanevski_contextual_modal_type_theory was developed for two main
purposes: support metaprogramming with open code, and capture the concept of metavariable
type-theoretically. It generalized the constructor $bold("quote") M : □A$ ($M$ is a closed term of type $A$)
from modal logic to $bold("box") (Γ. M)$ ($M$ may only depend on the variables in context $Γ$).

Actually, we have already been using metavariables without internalizing them into the type
system because all top level definitions, written as $p (x : A) (y_1 : A_1) ... (y_n : A_n) = P (x, y_1, ..., y_n)$
essentially give $p$ a contextual type $[y_1 : A_1, ..., y_n : A_n](x : A)$. That is, in #smallcaps("MPass") and #smallcaps("Sax"), process variables are metavariables.

1. First, in a mixed linear/nonlinear logic: What is the right decomposition of $[∆]A$ (which
requires a generalization of $↓$ or $↑$ or both)?
2. Prove admissibility of cut and identity in the sequent calculus formulation of contextual
mixed linear/nonlinear logic.
3. Give an operational interpretation, either under a message passing or a shared memory
interpretation.
4. Further questions to investigate:
  • Can we generalize the contextual linear/nonlinear logic to a full adjoint logic?
  • What additional computational or logical phenomena can be modeled by contextualizing adjoint logic (if any)?
*/

= Introduction

In logic, we consider hypothetical judgments $Γ ⊢ A$
and usually take them to mean "if every assumption in $Γ$ is true, then $A$ is true".
Nanevski et al.~@08nanevski_contextual_modal_type_theory introduced ICML,
Intuitionistic Contextual Modal Logic.
In ICML, $[Ψ]A$ is a proposition
standing for the hypothetical judgment $Ψ ⊢ A$.
So $[Ψ]A$ is true when
the truth of all assumptions in $Ψ$ implies truth of $A$.
In this way, ICML internalizes hypothetical truth in any context.
Nanevski and coauthors find $[Ψ]$ to be a modal operator validating S4 axioms.
Unfortunately, ICML is a structural logic.

In a different development,
Girard introduced linear logic @87girard_linear_logic
in which weakening and contraction are not available.
This enables tracking the exact multiset of assumptions (resources)
required to prove a statement (make a construction).
Linear logic is more general than structural logic:
Girard and Lafont @87girard_linear_logic_lazy_computation
showed that intuitionistic structural logic (IL)
can be soundly embedded into intuitionistic linear logic (ILL)
by means of an 'of course' operator $!$
that does admit weakeaning and contraction:

$ #prooftree(
  axiom($!Delta tack.r A$),
  rule($!Delta tack.r !A$, label: $!R$)
) #h(3em) #prooftree(
  axiom($Delta,A tack.r C$),
  rule($Delta, !A tack.r C$, label: $!L$)
) $
$ #prooftree(
  axiom($Delta tack.r C$),
  rule($Delta, !A tack.r C$, label: $sans("Wk")$)
) #h(3em) #prooftree(
  axiom($Delta,!A,!A tack.r C$),
  rule($Delta, !A tack.r C$, label: $sans("Ctr")$)
) $

In fact, 'of course' also satisfies the axioms of an S4 modality.

Andreoli @92andreoli_logic_programming_focusing_proofs_linear_logic
gave a _dyadic_ presentation of ILL,
meaning that the basic hypothetical judgment
assumes two contexts.
It is written (in our presentation) $Γ;Δ ⊢ A$
and read as
"if the structural assumptions in $Γ$ are valid, and the linear assumptions in $Δ$ are true, then the linear succedent $A$ is true".
In this presentation,
'of course' can be seen to internalize hypothetical truth
with no linear assumptions
(a construction that requires no resources):

$ #prooftree(
  axiom($Γ; dot ⊢ A$),
  rule($Γ; dot ⊢ !A$, label: $!R$)
) $

This brings forward the connection of ILL to ICML:
we conjecture that $!A ≡ [·]A$ should make sense somehow.

The 'of course' point of view treats ILL as prior,
and IL as something that embeds into it.
Benton @94benton_mixed_linear_non_linear_logic_proofs_terms_models
proposed an alternative perspective:
IL and ILL can be put on equal footing
in a combined system of linear/non-linear logic (LNL)
that includes two layers of propositions --
the structural ones and the linear ones --
that interact by means of up- and down-shift modalities $↑ ↓$.
In LNL, $!A eq.def #h(.3em) ↓↑ A$.

In this project we investigate how to combine these developments
by first making ICML linear
and then splitting the modality $[Ψ]$ into a contextual upshift $↑Ψ]$,
and a standard downshift $↓$ in the style of LNL.
We conjecture that $[Ψ]A ≡ #h(.3em) ↓↑Ψ] A$,
similarly to $!A ≡ [dot]A ≡ #h(.3em) ↓↑dot] A$.

The choice to generalize only the upshift, and not the downshift,
is motivated by the observation
that this seems to suffice to internalize hypothetical judgments
with respect to the _linear_ context.
However, other phenomena may not be captured.
We consider possible extensions in #ref(<further>).

= Development of the logical calculus

Nanevski and coauthors presented ICML as a system of natural deduction,
and an equivalent sequent calculus.
They provided an operational interpretation
for the former in the form of a type theory.
We present only a sequent calculus,
which will later be operationalized.

== The right left rule for $↑$

#let ctx = $sans("ctx")$

We start from Benton's LNL, presented as in lecture 10.
We have two basic judgments $Γ_S ⊢ A_S$
and $Γ_S; Δ_L ⊢ A_L$.
The shift rules are as follows:

#figure(
  grid(
    columns: (1fr, 1fr),
    [
      $ #prooftree(
        axiom($Γ_S;dot ⊢ A_L$),
        rule($Γ_S ⊢ ↑ A_L$, label: $↑ R$)
      ) $
      $ #prooftree(
        axiom($Γ_S ⊢ A_S$),
        rule($Γ_S;dot ⊢ ↓ A_S$, label: $↓ R$)
      ) $
    ],
    [
      $ #prooftree(
        axiom($Γ_S, ↑ A_L;Δ_L,A_L ⊢ C_L$),
        rule($Γ_S, ↑ A_L;Δ_L ⊢ C_L$, label: $↑ L$)
      ) $
      $ #prooftree(
        axiom($Γ_S, A_S;Δ_L ⊢ C_L$),
        rule($Γ_S;Δ_L, ↓ A_S ⊢ C_L$, label: $↓ L$)
      ) $
    ]
  ),
  caption: [Shift rules]
)

As mentioned earlier, we do not generalize the downshift.
So nothing will change in the downshift rules apart
from the intended interpretation of the symbols.

The remaining task is to generalize the upshift.
The right rule says that to prove $↑ A$,
it suffices to prove $A_L$ in an empty linear context.
It is clear how to make the linear context arbitrary:

$ #prooftree(
  axiom($Γ_S; Ψ_L ⊢ A_L$),
  rule($Γ_S ⊢ ↑ Ψ_L ] A_L$, label: $↑ R$)
) $

The left rule is not so easy:
at least syntactically,
there doesn't seem to be an empty context anywhere
that we could generalize.

One way of proceeding is to think of the rule $↑ L$
as a sort of cut:
we have the structural assumption $↑ A_L$
which means that we are assuming
that $A_L$ is provable from no linear assumptions.
Now the context $Δ_L$ is the same as $Δ_L,dot$,
and the rule $↑ L$ is cutting in $A_L$ for $dot$.
One possible generalization would consequently be
to cut in $A_L$ for some context $Ψ_L$:

$ #prooftree(
  axiom($Γ_S, ↑ Ψ_L ]A_L; Δ_L,A_L ⊢ C_L$),
  rule($Γ_S, ↑ Ψ_L ]A_L; Δ_L,Ψ_L ⊢ C_L$, label: $↑ L?$)
) $

Unfortunately this does not admit cut elimination,
for essentially the same reason that

$ #prooftree(
  axiom($Δ,B ⊢ C$),
  rule($Δ,A,A⊸B ⊢ C$)
) $

does not admit cut elimination in ILL.
In ILL with the above as the left rule for $⊸$,
#gbox($1⊸1 ⊢ 1$) has no cut-free proof because no rule applies.
This sequent is, however, provable with cut.
The reason is that the input to $⊸$
may not be directly available as an assumption
but rather only be provable
from a subcontext of $Δ$.
To remedy this, in ILL we must use

$ #prooftree(
  axiom($Δ' ⊢ A$),
  axiom($Δ,B ⊢ C$),
  rule($Δ,Δ',A⊸B ⊢ C$, n: 2)
) $

Similarly in our system with $↑ L?$,
#gbox($↑ 1 ]P;dot ⊢ P$) where $P$ is a propositional atom
has no cut-free proof, but is provable with cut.
To make the ILL remedy work,
we must express somehow
that _all_ propositions in the context $Ψ_L$ are provable.
We take a page from Nanevski and coauthors
and add a judgment $Γ_S; Δ_L ⊢ Ψ_L$
where the succedent is a linear context
derivable by

$ #prooftree(
  axiom($Γ_S;Δ_1 ⊢ A_1$),
  axiom($dots.h$),
  axiom($Γ_S;Δ_n ⊢ A_n$),
  rule($Γ_S;Δ_1, dots.h, Δ_n ⊢ A_1, dots.h, A_n$, n: 3, label: ctx)
) $

This extra gadget allows us to express the correct left rule

$ #prooftree(
  axiom($Γ_S, ↑ Ψ_L ]A_L; Δ'_L ⊢ Ψ_L$),
  axiom($Γ_S, ↑ Ψ_L ]A_L; Δ_L,A_L ⊢ C_L$),
  rule($Γ_S, ↑ Ψ_L ]A_L; Δ_L,Δ'_L ⊢ C_L$, n: 2, label: $↑L$)
) $

== Rules

In summary, the rules of our system are those of LNL
extended by a concludes-context judgment $Gamma_S;Delta_L tack.r Psi_L$
derivable by

$ #prooftree(
  axiom($Γ_S;Δ_1 ⊢ A_1$),
  axiom($dots.h$),
  axiom($Γ_S;Δ_n ⊢ A_n$),
  rule($Γ_S;Δ_1, dots.h, Δ_n ⊢ A_1, dots.h, A_n$, n: 3, label: ctx)
) $

and with the upshift rules replaced by

$ #prooftree(
  axiom($Γ_S; Ψ_L ⊢ A_L$),
  rule($Γ_S ⊢ ↑ Ψ_L ] A_L$, label: $↑ R$)
)\ #prooftree(
  axiom($Γ_S, ↑ Ψ_L ]A_L; Δ'_L ⊢ Ψ_L$),
  axiom($Γ_S, ↑ Ψ_L ]A_L; Δ_L,A_L ⊢ C_L$),
  rule($Γ_S, ↑ Ψ_L ]A_L; Δ_L,Δ'_L ⊢ C_L$, n: 2, label: $↑L$)
) $

We also note some essential properties of $↑$ and $↓$:

- $↑$ is invertible on the right, hence negative.
- $↓$ is invertible on the left, hence positive.

= Identity and cut elimination

#let cutSS = $sans("cut"_"SS")$
#let cutSL = $sans("cut"_"SL")$
#let cutLL = $sans("cut"_"LL")$
#let cutmLL = $sans("cut"_(overline("L")"L"))$
#let cutLmL = $sans("cut"_("L"overline("L")))$
#let cutSmL = $sans("cut"_("S"overline("L")))$
#let idS = $sans("id"_"S")$
#let idL = $sans("id"_"L")$
#let idmL = $sans("id"_overline("L"))$

We will show that the following rules of identity and cut
are admissible in a version of our system without cut,
and with identites restricted to atomic propositions.
We will rely on the fact that the system we adapted, LNL,
has these properties.

#figure(
  $ #prooftree(
    rule($Γ_S,A_S ⊢ A_S$, n: 0, label: idS)
  ) #h(3em) #prooftree(
    rule($Γ_S;A_L ⊢ A_L$, n: 0, label: idL)
  ) $,
  caption: [Identity rules]
)

#figure(
  [
    $ #prooftree(
      axiom($Γ_S ⊢ A_S$),
      axiom($Γ_S,A_S ⊢ C_S$),
      rule($Γ_S ⊢ C_S$, n: 2, label: cutSS)
    ) \
    #prooftree(
      axiom($Γ_S ⊢ A_S$),
      axiom($Γ_S,A_S;Δ_L ⊢ C_L$),
      rule($Γ_S;Δ_L ⊢ C_L$, n: 2, label: cutSL)
    ) \
    #prooftree(
      axiom($Γ_S;Δ'_L ⊢ A_L$),
      axiom($Γ_S;Δ_L,A_L ⊢ C_L$),
      rule($Γ_S;Δ_L,Δ'_L ⊢ C_L$, n: 2, label: cutLL)
    ) $
  ],
  caption: [Cut rules]
)

#lemma("Identity for contexts")[
If $Gamma_S;A_L ⊢ A_L$ is derivable for every $A_L in Psi_L$, then
$ #prooftree(
  rule($Γ_S;Psi_L ⊢ Psi_L$, n: 0, label: idmL)
) $
is derivable.
]
#proof[
Let $Psi_L = A_1, dots.h, A_n$. Then

$ #prooftree(
  axiom($Gamma_S;A_1 ⊢ A_1$),
  axiom($dots.h$),
  axiom($Gamma_S;A_n ⊢ A_n$),
  rule($Gamma_S;A_1, dots.h, A_n ⊢ A_1, dots.h, A_n$, n: 3, label: ctx)
) $
]

#theorem("Admissibility of Identity")[
The rules of identity #idS and #idL are admissible
in the system where identities are restricted to atomic propositions.
]
#proof[
By simultaneous structural induction on $A_S$ and $A_L$.
The cases except for $↑$
are the same as in LNL,
so need not be re-checked.
The new case of #idS follows by #idmL since all propositions in $Psi_L$
are subformulas of $↑Psi_L]A_L$.

$ #prooftree(
  rule($Γ_S,↑Psi_L]A_L;Psi_L ⊢ Psi_L$, n: 0, label: idmL),
  rule($Γ_S,↑Psi_L]A_L;A_L ⊢ A_L$, n: 0, label: idL),
  rule($Γ_S,↑Psi_L]A_L;Psi_L ⊢ A_L$, n: 2, label: $↑ L$),
  rule($Γ_S,↑Psi_L]A_L ⊢ ↑ Psi_L]A_L$, label: $↑ R$)
) $
]

#lemma("Cut for contexts")[
If #cutSL with $cal(D)$ and any subderivation of $cal(E)$
as premises is admissible,
then
$ #prooftree(
  axiom($Γ_S ⊢ A_S$, label: $cal(D)$),
  axiom($Γ_S,A_S;Delta_L ⊢ Psi_L$, label: $cal(E)$),
  rule($Γ_S;Δ_L ⊢ Psi_L$, n: 2, label: cutSmL)
) $
is derivable.
Similarly if #cutLL with $cal(D)$ and any subderivation of $cal(E)$
as premises is admissible,
then
$ #prooftree(
  axiom($Γ_S;Delta'_L ⊢ A_L$, label: $cal(D)$),
  axiom($Γ_S;Delta_L, A_L ⊢ Psi_L$, label: $cal(E)$),
  rule($Γ_S;Δ_L, Delta'_L ⊢ Psi_L$, n: 2, label: cutLmL)
) $
is derivable.
Furthermore if #cutLL with any subderivation of $cal(D)$
as the left permise is admissible,
then for all $cal(E)$
$ #prooftree(
  axiom($Γ_S;Delta'_L ⊢ Psi_L$, label: $cal(D)$),
  axiom($Γ_S;Delta_L, Psi_L ⊢ C_L$, label: $cal(E)$),
  rule($Γ_S;Δ_L, Delta'_L ⊢ C_L$, n: 2, label: cutmLL)
) $
is derivable.
]
#proof[
(#cutSmL). Let $Psi_L = B_1, dots.h, B_n$.
By inversion on $cal(E)$ (which was derived by #ctx),
there are contexts ${Delta_i}$ such that $Delta_L = Delta_1, dots.h, Delta_n$,
and $Gamma_S,A_S;Delta_i ⊢ B_i$ are all derivable.
Thus
$ #prooftree(
  axiom($Γ_S ⊢ A_S$),
  axiom($Γ_S,A_S;Delta_1 ⊢ B_1$),
  rule($Γ_S;Δ_1 ⊢ B_1$, n: 2, label: cutSL),
  axiom($dots.h$),
  axiom($Γ_S ⊢ A_S$),
  axiom($Γ_S,A_S;Delta_n ⊢ B_n$),
  rule($Γ_S;Δ_n ⊢ B_n$, n: 2, label: cutSL),
  rule($Γ_S;Δ_L ⊢ B_1, dots.h, B_n$, n: 3, label: ctx)
) $

(#cutLmL).
Let $Psi_L = B_1, dots.h, B_n$.
By inversion on $cal(E)$,
there are contexts ${Delta_i}$ such that $Delta_L,A_L = Delta_1, dots.h, Delta_n$,
and $Gamma_S;Delta_i ⊢ B_i$ are all derivable.
Let $Delta_(i_0)$ be the context that contains $A_L$.
We now have

$ #prooftree(
  axiom($Γ_S;Δ_1 ⊢ B_1$),
  axiom($dots.h$),
  axiom($Γ_S;Delta'_L ⊢ A_L$, label: $cal(D)$),
  axiom($Γ_S;Delta_(i_0) ⊢ B_(i_0)$),
  rule($Γ_S;Δ_(i_0) - {A_L}, Δ'_L ⊢ B_(i_0)$, n: 2, label: cutLL),
  axiom($dots.h$),
  axiom($Γ_S;Δ_n ⊢ B_n$),
  rule($Γ_S;Δ_L, Δ'_L ⊢ Psi_L$, n: 5, label: ctx)
) $

(#cutmLL). Let $Psi_L = A_1, dots.h, A_n$.
By inversion on $cal(D)$,
there are contexts ${Delta'_i}$ such that $Delta'_L = Delta'_1, dots.h, Delta'_n$
and $Gamma_S;Delta'_i ⊢ A_i$ are all derivable.
We now have

$ #prooftree(
  axiom($Γ_S;Delta'_1 ⊢ A_1$),
  axiom($Γ_S;Delta'_2 ⊢ A_2$),
  axiom($Gamma_S;Delta_L,Psi_L tack.r C_L$, label: $cal(E)$),
  rule($dots.v$),
  rule($Γ_S;Delta_L,A_1,Delta'_2,dots.h,Delta'_n ⊢ C_L$, n: 2, label: cutLL),
  rule($Γ_S;Δ_L, Delta'_1, dots.h, Delta'_n ⊢ C_L$, n: 2, label: cutLL)
) $

]

#theorem("Admissibility of Cut")[
The three rules of cut are admissible in the system without cut.
]
#proof[
By simultaneous nested induction on all three forms of cut,
first on the cut proposition $A_L$ or $A_S$,
and second on the first and second given derivation.
Both LNL without cut and our system without cut
have the subformula property.
Thus, cut-free proofs of connectives other than $↑$
cannot refer to $↑$.
Consequently the cases of cut elimination for these connectives
are the same as in the proof for LNL
and need not be re-checked.

We only need to check cases with the modified $↑$ connective.
We only consider principal and commuting cases.

The *principal case* of #cutSL $↑R slash ↑L$ is

$ #prooftree(
  axiom($Γ_S;Psi_L ⊢ A_L$, label: $cal(D)$),
  rule($Γ_S ⊢ ↑ Psi_L]A_L$, label: $↑ R$),
  axiom($Γ_S, ↑ Psi_L]A_L;Δ'_L ⊢ Psi_L$, label: $cal(E_1)$),
  axiom($Γ_S, ↑ Psi_L]A_L;Δ_L,A_L ⊢ C_L$, label: $cal(E_2)$),
  rule($Γ_S, ↑ Psi_L]A_L;Δ_L,Δ'_L ⊢ C_L$, n: 2, label: $↑L$),
  rule($Γ_S;Δ_L,Δ'_L ⊢ C_L$, n: 2, label: cutSL)
) $

and eliminates to

$ #prooftree(
  axiom($cal(A)$),
  axiom($Γ_S;Psi_L ⊢ A_L$, label: $cal(D)$),
  axiom($Γ_S ⊢ ↑ Psi_L]A_L$, label: $cal(D')$),
  axiom($Γ_S, ↑ Psi_L]A_L;Δ_L,A_L ⊢ C_L$, label: $cal(E_2)$),
  rule($Γ_S;Δ_L,A_L ⊢ C_L$, n: 2, label: cutSL),
  rule($Γ_S;Δ_L,Psi_L ⊢ C_L$, n: 2, label: cutLL),
  rule($Γ_S;Δ_L,Δ'_L ⊢ C_L$, n: 2, label: cutmLL)
) $

// TODO: draw a brace around $cal(D')$ in the unreduced proof?
where $cal(D') = cal(D)+↑ R$, and $cal(A)$ is

$ #prooftree(
  axiom($Γ_S ⊢ ↑Psi_L]A_L$, label: $cal(D')$),
  axiom($Γ_S, ↑Psi_L]A_L;Δ'_L ⊢ Psi_L$, label: $cal(E_1)$),
  rule($Γ_S;Δ'_L ⊢ Psi_L$, n: 2, label: cutSmL)
) $

Note that the use of #cutmLL on $Psi_L$ is justified
because all formulas in $Psi_L$ are subformulas of $arrow.t Psi_L]A_L$,
and the use of #cutSmL is justified
because $cal(E)_1$ is a smaller derivation.

The *commuting case* of #cutLL with $↑L slash ?$ is

$ #prooftree(
  axiom($Γ_S, ↑ Ψ_L ]A_L; Δ'_L ⊢ Ψ_L$, label: $cal(D)_1$),
  axiom($Γ_S, ↑ Ψ_L ]A_L; Δ_L,A_L ⊢ C_L$, label: $cal(D)_2$),
  rule($Γ_S, ↑ Ψ_L ]A_L; Δ_L,Δ'_L ⊢ C_L$, n: 2, label: $↑L$),
  axiom($Γ_S, ↑ Ψ_L ]A_L;Δ''_L,C_L ⊢ D_L$, label: $cal(E)$),
  rule($Γ_S, ↑ Ψ_L ]A_L;Δ_L,Δ'_L,Δ''_L ⊢ D_L$, n: 2, label: cutLL)
) $

This eliminates to

$ #prooftree(
  axiom($Γ_S, ↑ Ψ_L ]A_L; Δ'_L ⊢ Ψ_L$, label: $cal(D)_1$),
  axiom($Γ_S, ↑ Ψ_L ]A_L; Δ_L,A_L ⊢ C_L$, label: $cal(D)_2$),
  axiom($Γ_S, ↑ Ψ_L ]A_L;Δ''_L,C_L ⊢ D_L$, label: $cal(E)$),
  rule($Γ_S, ↑ Ψ_L ]A_L;Δ_L,A_L,Δ''_L ⊢ D_L$, n: 2, label: cutLL),
  rule($Γ_S, ↑ Ψ_L ]A_L;Δ_L,Δ'_L,Δ''_L ⊢ D_L$, n: 2, label: $↑ L$)
) $

The *commuting case* of #cutSS with $? slash ↑R$ is

$ #prooftree(
  axiom($Γ_S ⊢ A_S$, label: $cal(D)$),
  axiom($Γ_S,A_S;Psi_L ⊢ B_L$, label: $cal(E)$),
  rule($Γ_S,A_S ⊢ ↑ Psi_L]B_L$, label: $↑ R$),
  rule($Γ_S ⊢ ↑ Psi_L]B_L$, n: 2, label: cutSS)
) $

This eliminates to

$ #prooftree(
  axiom($Γ_S ⊢ A_S$, label: $cal(D)$),
  axiom($Γ_S,A_S;Psi_L ⊢ B_L$, label: $cal(E)$),
  rule($Γ_S; Psi_L ⊢ B_L$, n: 2, label: cutSS),
  rule($Γ_S ⊢ ↑ Psi_L]B_L$, label: $↑ R$)
) $

The *commuting case* of #cutSL with $? slash ↑ L$ is

$ #prooftree(
  axiom($Γ_S ⊢ A_S$, label: $cal(D)$),
  axiom($Γ_S, A_S, ↑ Psi_L]A_L; Δ_L ⊢ Psi_L$, label: $cal(E)_1$),
  axiom($Γ_S, A_S, ↑ Psi_L]A_L; Δ'_L, A_L ⊢ C_L$, label: $cal(E)_2$),
  rule($Γ_S, A_S, ↑ Psi_L]A_L;Δ_L,Δ'_L ⊢ C_L$, n: 2, label: $↑ L$),
  rule($Γ_S, ↑ Psi_L]A_L;Δ_L,Δ'_L ⊢ C_L$, n: 2, label: cutSL)
) $

and eliminates to

$ #prooftree(
  axiom($Γ_S ⊢ A_S$, label: $cal(D)$),
  axiom($Γ_S, A_S, ↑ Psi_L]A_L; Δ_L ⊢ Psi_L$, label: $cal(E)_1$),
  rule($Γ_S, ↑ Psi_L]A_L; Δ_L ⊢ Psi_L$, n: 2, label: cutSmL),
  axiom($Γ_S ⊢ A_S$, label: $cal(D)$),
  axiom($Γ_S, A_S, ↑ Psi_L]A_L; Δ'_L, A_L ⊢ C_L$, label: $cal(E)_2$),
  rule($Γ_S, ↑ Psi_L]A_L; Δ'_L, A_L ⊢ C_L$, n: 2, label: cutSL),
  rule($Γ_S, ↑ Psi_L]A_L;Δ_L,Δ'_L ⊢ C_L$, n: 2, label: $↑L$)
) $

Finally, #cutLL with $? slash ↑ L$ has two *commuting cases*
depending on which branch uses $B_L$.
The first is

$ #prooftree(
  axiom($Γ_S, ↑ Psi_L]A_L; Δ'_L ⊢ B_L$, label: $cal(D)$),
  axiom($Γ_S, ↑ Psi_L]A_L; Δ_1, B_L ⊢ Psi_L$, label: $cal(E)_1$),
  axiom($Γ_S, ↑ Psi_L]A_L; Δ_2, A_L ⊢ C_L$, label: $cal(E)_2$),
  rule($Γ_S, ↑ Psi_L]A_L;Δ_1,Δ_2,B_L ⊢ C_L$, n: 2, label: $↑ L$),
  rule($Γ_S, ↑ Psi_L]A_L;Δ_1,Δ_2,Δ'_L ⊢ C_L$, n: 2, label: cutLL)
) $

We first do a sub-cut to obtain derivation $cal(A)$:

$ #prooftree(
  axiom($Γ_S, ↑ Psi_L]A_L;Δ'_L ⊢ B_L$, label: $cal(D)$),
  axiom($Γ_S, ↑ Psi_L]A_L;Δ_1, B_L ⊢ Psi_L$, label: $cal(E)_1$),
  rule($Γ_S, ↑ Psi_L]A_L;Δ_1, Δ'_L ⊢ Psi_L$, n: 2, label: cutLmL)
) $

The use of #cutLmL is justified here because $cal(E)_1$
is a smaller derivation. Then we can eliminate to

$ #prooftree(
  axiom($Γ_S, ↑ Psi_L]A_L;Δ_1, Δ'_L ⊢ Psi_L$, label: $cal(A)$),
  axiom($Γ_S, ↑ Psi_L]A_L; Δ_2, A_L ⊢ C_L$, label: $cal(E)_2$),
  rule($Γ_S, ↑ Psi_L]A_L;Δ_1,Δ_2,Δ'_L ⊢ C_L$, n: 2, label: $↑ L$)
) $

The *second* is

$ #prooftree(
  axiom($Γ_S, ↑ Psi_L]A_L; Δ'_L ⊢ B_L$, label: $cal(D)$),
  axiom($Γ_S, ↑ Psi_L]A_L; Δ_1, ⊢ Psi_L$, label: $cal(E)_1$),
  axiom($Γ_S, ↑ Psi_L]A_L; Δ_2, B_L, A_L ⊢ C_L$, label: $cal(E)_2$),
  rule($Γ_S, ↑ Psi_L]A_L;Δ_1,Δ_2,B_L ⊢ C_L$, n: 2, label: $↑ L$),
  rule($Γ_S, ↑ Psi_L]A_L;Δ_1,Δ_2,Δ'_L ⊢ C_L$, n: 2, label: cutLL)
) $

We first obtain $cal(A)$:

$ #prooftree(
  axiom($Γ_S, ↑ Psi_L]A_L;Δ'_L ⊢ B_L$, label: $cal(D)$),
  axiom($Γ_S, ↑ Psi_L]A_L;Δ_2, B_L, A_L ⊢ C_L$, label: $cal(E)_2$),
  rule($Γ_S, ↑ Psi_L]A_L;Δ_2, Δ'_L, A_L ⊢ C_L$, n: 2, label: cutLL)
) $

And then produce the new proof:

$ #prooftree(
  axiom($Γ_S, ↑ Psi_L]A_L; Δ_1 ⊢ Psi_L$, label: $cal(E)_1$),
  axiom($Γ_S, ↑ Psi_L]A_L;Δ_2, Δ'_L, A_L ⊢ C_L$, label: $cal(A)$),
  rule($Γ_S, ↑ Psi_L]A_L;Δ_1,Δ_2,Δ'_L ⊢ C_L$, n: 2, label: $↑L$)
) $

]

= Operational interpretation

#let recv = $sans("recv")$
#let send = $sans("send")$
#let proc = $sans("proc")$
#let call = $sans("call")$

We extend the operational interpretation
of LNL proofs as message passing programs
to our system.

The program terms for LNL rules are as before.
A provider of generalized upshift type $↑Psi_L]A_L$
provides a structural channel
that expects to receive the resources $Psi_L$
and continues by providing a channel of type $A_L$.
In essence, it is like a global #smallcaps("MPass") function $times.circle.big_i Psi_i multimap A_L$
(registered with `proc`)
that can be called arbitrarily many times,
but now existing dynamically as a channel.

Writing $overline(t_i)$ for an arbitrary list of terms $t_1,dots.h,t_n$,
our program terms written in send-receive style are:

#figure(
  [
    $ #prooftree(
      axiom($Γ_S;overline(x_i):Psi_L ⊢ P(overline(x_i),y_L) :: (y_L:A_L)$),
      rule($Γ_S ⊢ recv f_S space (⟨y_L⟩, overline(⟨x_i⟩) => P) :: (f_S:↑ Psi_L]A_L)$, label: $↑ R$)
    ) $

    $ #prooftree(
      axiom($Γ_S,f_S:↑ Psi_L]A_L;Δ_L ⊢ overline(P_i (x_i)) :: (overline(x_i):Psi_L)$),
      axiom($Γ_S,f_S:↑ Psi_L]A_L;Δ'_L,y_L:A_L ⊢ Q(y_L) :: (z_L:C_L)$),
      rule($Γ_S,f_S:↑ Psi_L]A_L;Δ_L,Δ'_L ⊢ send f_S space overline((⟨x_i⟩ => P_i)) space (⟨y_L⟩ => Q) :: (z_L:C_L)$, n: 2, label: $↑ L$)
    ) $
  ],
  caption: [Upshift program terms]
)

We could alternatively use a syntax closer to the one in #smallcaps("MPass") by writing:
- $proc f_S space (y_L:A_L) space overline((x_i:A_i)) = P$ for $recv f_S space (⟨y_L⟩, overline(⟨x_i⟩) => P)$
- $call f_S space overline((x_i => P_i)) space (⟨y_L⟩ => Q)$ for $send f_S space overline((x_i => P_i)) space (⟨y_L⟩ => Q)$
although the analogy is not exact:
e.g. the argument $P_i$ to $call$
is a program term that writes into a freshly bound channel
rather than necessarily being a variable
as in the original $call$ syntax.

The dynamic behaviour inspired by the principal case of cut elimination for $arrow.t$ is:

$ & underline(proc) (recv a_S space (⟨y_L⟩, overline(⟨x_i⟩) => P)), proc (send a_S space overline((⟨x_i⟩ => Q_i)) space (⟨y_L⟩ => R)) --> \
& underline(proc) (dots.h), overline(proc(Q_i (b_i))), proc(P(overline(b_i),c_L)), proc (R(c_L)) $

Insofar as the operation consists of the persistent provider
receiving several channels at once,
we may need to adjust the message grammar to $M ::= dots.h | ⟨overline(a_i)⟩$.

= Further questions <further>

- We chose to generalize $arrow.t$ to $↑ Psi_L]A_L$.
  Alternatively, we could also capture the structural context
  as in $↑Γ_S;Psi_L]A_L$
  with the right rule
  $ #prooftree(
    axiom($Gamma_S;Psi_L tack.r A_L$),
    rule($Theta_S tack.r ↑Γ_S;Psi_L]A_L$)
  ) $
  This formulation would more clearly include the structural ICML
  in its structural fragment; our current version seems to include
  something like a linear version of ICML in its linear fragment instead.
- Can $arrow.b$ be contextified, too, and how?
  Does it have anything to do with existential quantification or parametric abstraction?
- How does any of this generalize to a full adjoint logic?
- Can our additions be reflected in the categorical semantics of LNL
  @94benton_mixed_linear_non_linear_logic_proofs_terms_models
  without modifying the notion of model?
  In other words, is the extension conservative?

/* WARNING: speculation, might be wrong

== Categorical semantics

Benton @94benton_mixed_linear_non_linear_logic_proofs_terms_models
showed that a categorical model
of the multiplicative ($times.circle, multimap, 1$) fragment of LNL can be built out of the data of
- a cartesian closed category $(cal(C), 1, times, arrow)$; and
- a symmetric monoidal closed category $(cal(L), bold(I), times.circle, multimap)$; and
- a pair of symmetric monoidal functors $(arrow.t, n) : cal(L) arrow cal(C)$,
  $(arrow.b, m) : cal(C) arrow cal(L)$
  that form a symmetric monoidal adjunction $arrow.b tack.l arrow.t$.

As one consequence of this definition,
there is a natural isomorphism
$m_(A,B) : arrow.b A times.circle arrow.b B tilde.equiv arrow.b (A times B)$
and an isomorphism $m_I : bold(I) tilde.equiv arrow.b 1$.

Given this data,
we interpret linear types as objects in $cal(L)$,
and structural types as objects in $cal(C)$.
This lifts to linear and structural contexts
using the monoidal and cartesian product operations,
respectively.
A proof of
$ Gamma_1, dots.h, Gamma_n;Delta_1, dots.h, Delta_m tack.r A_L $
becomes a morphism
$ times.circle.big_(1<=i<=n) arrow.b Gamma_i times.circle times.circle.big_(1<=j<=m) Delta_j arrow A in cal(L) $
whereas a proof of
$ Gamma_1, dots.h, Gamma_n tack.r A_S $
becomes a morphism
$ product_(1<=i<=n) Gamma_i arrow A in cal(C) $
where we punned types and their interpretations.

We conjecture that a possible interpretation of $arrow.t Psi_1, dots.h, Psi_n]A_L$
comes from the exponential object via $arrow.t (times.circle.big_(1<=i<=n)Psi_i multimap A)$.
Below we check that this makes the two rules for $arrow.t$ interpretable.
However, we do not check that our cut elimination procedure is sound
with respect to this interpretation.

... */

#bibliography("papers.bib", style: "association-for-computing-machinery")
