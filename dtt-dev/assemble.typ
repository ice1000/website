#let setup-authors(authors) = {
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
#import "config.typ": *
#show: dtt.with(title: "Dependent Theory of Types")

#setup-authors(((
  name: "Tesla Zhang",
  email: "teslaz@cmu.edu"
),))

#set heading(numbering: "1.")
#outline(depth: 2, indent: auto)
#import "@preview/fletcher:0.4.3" as fletcher: diagram, node, edge
#let cedge(..args) = edge(label-side: center, ..args)
#set quote(block: true)

= Introduction
This is an extremely syntax-minded development on some meta-level dependent type theory,
which I wish to convey an interesting perspective.
Experienced readers will immediately know what I'm trying to do in this development, but I will not spoil it here.

The type theory I consider here is not designed to be implementable (i.e. have decidable type checking)
or practical, but rather intended to be a reasoning framework about constructions.
I will also try to avoid set theoretic terminologies as much as possible,
and restrict the prerequisites to only mathematical maturity.

In the whole development, I will assume nameless representation of variables, and treat them informally as if they are named.

For readers who are unfamiliar with logic, here are two notions that will be used frequently:

#definition("Derivable")[
A _derivable_ judgment in a type theory is a judgment one may derive using the typing rules.
]
#definition("Admissible")[
An _admissible_ rule in a type theory is a rule that can be proved at the meta level by doing case analysis on the premises.
]
The usual definition of admissibility is that it does not add new theorems to the theory,
but I personally find it too much of a characterization, and is far from something we can easily verify.

In practice, it's most likely the case that admissible rules are proved by case analysis on the premises,
which is usually clearer how to do.

= Substitution Calculus <sec:subst-calculus>
The goal of this chapter is to defined a _substitution calculus_, which a dependent type theory with a well-behaved substitution operation.

== Judgments

// CwF
#definition("Judgment schema")[
We assume the following judgment schemas of type theories:

+ $Γ ⊢$ means $Γ$ is a well-formed context.
+ $Γ ⊢ A$ means $A$ is a well-typed type in context $Γ$.
+ $Γ ⊢ A ≡ B$ means $A$ and $B$ are equal types in $Γ$.
+ $Γ ⊢ a : A$ means $a$ is a well-typed term of type $A$ in $Γ$.
+ $Γ ⊢ a ≡ b : A$ means $a$ and $b$ are equal terms of type $A$ in $Γ$.
+ $Γ ⊢ σ : Δ$ means $σ$ is a substitution object from $Γ$ to $Δ$.
+ $Γ ⊢ σ ≡ γ : Δ$ means $σ$ and $γ$ are equal substitution objects from $Γ$ to $Δ$.
]

The equality relation imposed by the judgments are called _judgmental equality_, which is the meta-level equality we will be working with throughout the development.

In fact, we don't necessarily need $Γ ⊢ A$, $Γ ⊢ a : A$, and $Γ ⊢ σ : Δ$, as they can be seen as reflexive case of the equality judgments, but we keep them regardless for better readability.

Some notational conventions:
+ For empty contexts and substitutions, we overload the symbol $·$ to represent both of them, usually wrapped in parentheses.
+ When a part of a judgment is clear from the context and writing it down will significantly distract the reader, we omit it. For instance, when talking about the equality between some terms, we may omit the context and the type.

// A Bob Harper thing
#definition("Presuppositions")[
The judgments come with _presuppositions_ that are always assumed:

+ $Γ ⊢ A$ presupposes $Γ ⊢$.
+ $Γ ⊢ A ≡ B$ presupposes $Γ ⊢ A$ and $Γ ⊢ B$.
+ $Γ ⊢ a : A$ presupposes $Γ ⊢ A$.
+ $Γ ⊢ a ≡ b : A$ presupposes $Γ ⊢ a : A$ and $Γ ⊢ b : A$.
+ $Γ ⊢ σ : Δ$ presupposes $Γ ⊢$ and $Δ ⊢$.
+ $Γ ⊢ σ ≡ γ : Δ$ presupposes $Γ ⊢ σ : Δ$ and $Γ ⊢ γ : Δ$.

When we write down a rule that derives a judgment, we implicitly assume that the presuppositions are in the premises.
] <def:presup>

// For expert readers: unless explicitly stated otherwise, the type theory we consider will be structural type theories without modalities or type universes -- so that all type formers are well-behaved and simple.

#definition[We assume judgmental equality to be _reflexive_:
$ Γ ⊢ A ≡ A #h(2em) Γ ⊢ a ≡ a : A $
] <def:refl:jeq>

#definition[We assume judgmental equality to be _substitutive_.]
This is very hard to spell out formally in a general setting, but it basically means that we can substitute equal terms in any judgment.
We provide two example special cases of this principle to illustrate its meaning:

#corollary[
We assume the equality judgments to be symmetric, and transitive:
$ (Γ ⊢ A ≡ B)/(Γ ⊢ B ≡ A) #h(2em) (Γ ⊢ a ≡ b : A)/(Γ ⊢ b ≡ a : A) \
  (Γ ⊢ A ≡ B #h(2em) Γ ⊢ B ≡ C)/(Γ ⊢ A ≡ C) \
  (Γ ⊢ a ≡ b : A #h(2em) Γ ⊢ b ≡ c : A)/(Γ ⊢ a ≡ c : A)
 $
]
#proof[
- Symmetry: $Γ ⊢ A ≡ B$ so we can replace $B$ with $A$, and the goal becomes $Γ ⊢ A ≡ A$,
  which holds by @def:refl:jeq. The one for terms is similar.
- Transitivity: $Γ ⊢ A ≡ B$, so we can replace $B$ with $A$ so the other premise becomes $Γ ⊢ A ≡ C$,
  which is equal to the goal.
]

#corollary[
Typing of terms is up to judgmental equality of types:
$ (Γ ⊢ A ≡ B #h(2em) Γ ⊢ a:B)/(Γ ⊢ a:A) $
] <def:typing:jeq>
#proof[$Γ ⊢ A ≡ B$ so we can replace $B$ with $A$ in the premise, which makes it equal to the goal.]

Furthermore, we assume all the congruence rules (i.e. all functions are pure) for the equality judgments, which are omitted everywhere for brevity.

== Contexts and Substitutions

// Context comprehension
#definition("Context")[
A well formed context is inductively generated by the following rules:

$ (·) ⊢ #h(2em) (Γ⊢A)/(Γ,x:A⊢) $

The symbol $·$ denotes an empty context (with parenthesis for clarification purpose),
and $Γ,x:A$ denotes the adding $x:A$ to $Γ$.
]

When the variable in the context is insignificant, we may omit it, and simply write $Γ,A$.

// Base-change functors
#definition("Substitution action")[
For a substitution object $Γ ⊢ σ : Δ$, we define the _action_ of substitution on types and terms as follows:
$ (Δ ⊢ A)/(Γ ⊢ A[σ]) #h(2em) (Δ ⊢ a : A)/(Γ ⊢ a[σ] : A[σ]) \
  (Δ ⊢ A ≡ B)/(Γ ⊢ A[σ] ≡ B[σ]) #h(2em) (Δ ⊢ a ≡ b : A)/(Γ ⊢ a[σ] ≡ b[σ] : A[σ]) $
]

In PFPL, $A[σ]$ is denoted $hat(σ)(A)$.
Note that the exact behavior of this operation is not specified yet.

Next, we define _substitution object_, which is a list of "term-variable" pairs ($a"/"x$), meaning _replacing the variable $x$ with the term $a$_. A list of such thing looks like $(a"/"x, b"/"y, c"/"z,...)$, meaning that we intend to do all of these substitutions.
#definition("Substitution object")[
A substitution object is inductively generated by the following rules:

+ $ Γ ⊢ (·) : (·) $
  Similar to contexts, $·$ denotes an empty substitution object, and the type of an empty substitution object is the empty context.
+ $ (Γ⊢σ:Δ #h(2em) Γ⊢A \ Γ⊢a:A[σ])/(Γ⊢(σ,a "/" x):(Δ,x:A)) $
When the $x$ in $(σ,a "/" x)$ is clear from the context, we may omit it, and simply write $(σ,a)$.
]

So, contexts are telescopic lists of types, and substitutions are telescopic list of terms which can be used to substitute variables.

For equality of substitutions, we intend to equate them according to their actions. In other words, two substitutions are equal if they act the same way on types and terms.
#definition("Substitution extensionality")[
If for every $Γ ⊢ A$, $Γ ⊢ A[σ] ≡ A[γ]$, and for every $Γ ⊢ a : A$, $Γ ⊢ a[σ] ≡ a[γ]$, then:
$ Γ ⊢ σ ≡ γ : Δ $
] <def:subst:ext>

We assume substitution to have some commonly expected properties,
which includes having an identity and compose associatively.
But in order to define those, we need to define variables introduction.

#definition("Containment")[
We define the judgment $x:A ∈_n Γ$ to mean that $x$ is the $n$-th variable in the context $Γ$,
counting from the left, and is of type $A$. The judgment is generated by the following rules:

+ $x:A ∈_n (Γ,x:A)$ for the length of $Γ$ being $n$,
+ $ (x:A ∈_n Γ)/(x:A ∈_n (Γ,y:B)) $
  Extending the context does not change the level.
]
#example[
+ $x:A ∈_0 (x:A)$
+ $x:A ∈_0 (x:A,y:B)$
+ $y:B ∈_1 (x:A,y:B)$
]

For readers familiar with implementation of type theories,
this is the same as de Bruijn levels, aka code Bruijn indices.
We are using a locally nameless á la McBride approach, which uses levels for variables from the context.

#definition("Variable")[
We assume the following rule:
$ (x:A ∈_n Γ)/(Γ ⊢ x:A) $
such that $x[σ]$ is defined as the $n$-th term in the substitution object $σ$.
]

// Identity morphism
#construction("Identity substitution")[
For any context $Γ$, we define $Γ ⊢ id_Γ : Γ$ to be the following substitution object by induction on $Γ$:
+ $Γ = (·)$, then $id_((·)) := (·)$.
+ $Γ = Γ',x:A$, then $id_(Γ',x:A) := (id_(Γ'),x)$, where $Γ ⊢ x:A$.
] <cons:id:subst>

#lemma[Idenity substitution actions are identity functions:
$ Γ ⊢ A[id_Γ] ≡ A #h(2em) Γ ⊢ a[id_Γ] ≡ a : A $]

// Composition of morphisms
#construction("Composition of substitutions")[
For any substitution objects $Γ ⊢ σ : Δ$ and $Δ ⊢ γ : Θ$, we denote $Γ ⊢ (γ∘σ) : Θ$ to be the substitution object formed by induction on $γ$:

+ $γ = (·)$, which implies $Θ = (·)$, we define $(·∘σ) = σ$.
+ $γ = (γ',a)$, which implies $Θ = (Θ',x:A)$, we define $((γ',a)∘σ) = ((γ'∘σ),a[σ])$.
]

#lemma[Composition of substitutions is associative: $ (γ∘σ)∘ρ ≡ γ∘(σ∘ρ) $]
#lemma[Composition of substitutions is unital: $ (id∘σ) ≡ (σ∘id) ≡ σ $]
#lemma[Composition of substitutions commutes with substitution action: $ A[γ∘σ] ≡ A[σ][γ] #h(2em) a[γ∘σ] ≡ a[σ][γ] $]
Note that the order of composition of substitutions is reversed when applying them as actions.

#definition("Context isomorphism")[
A substitution $Γ ⊢ σ : Δ$ is called a _context isomorphism_ if there exists $Δ ⊢ γ : Γ$ such that $σ∘γ ≡ id_Δ$ and $γ∘σ ≡ id_Γ$.
We denote isomorphic contexts as $Γ ≃ Δ$.
]
#lemma[Composition of context isomorphisms will also be context isomorphisms.]
#proof[By composing their inverse to get the inverse of the composite.]

// Display maps
#construction("Projection")[For any type $Γ⊢A$,
we define $Γ,x:A ⊢π_A : Γ$ to be the identity substitution object $id_Γ$ weakened by $A$.]

An alternative way to think about $π_A$ is that it is the substitution
object that deletes the last variable from the context, and acts as the identity substitution otherwise.

== Structural properties

Since we already have weakening, we further require that the weakening substitution is an inclusion.

#definition("Weakening")[
The substitution action induced by any projection is an identity:
$ (Γ⊢A #h(2em) Γ⊢B)/(Γ,x:A⊢B[π_A] ≡ B) #h(2em)
  (Γ⊢b:B)/(Γ,x:A⊢b[π_A]≡b : B)
 $
]

#lesson("Pain")[If weakening is an inclusion, the variable rule becomes very easy to write down,
we can simply say: $ Γ ⊢ x : A $
if $A$ is not at the end of the context and weakening is not an inclusion,
we would have to write: $ Γ ⊢ x : A[π_B_1][π_B_2]... $
where $π_B_1,π_B_2,...$ are the projections that delete the types before $A$.]

In our case, since weakening substitutions behave like inclusions, we can omit all of them.

#theorem("Exchange")[
For types $Γ⊢A$ and $Γ⊢B$, we have the following context isomorphism:
$ Γ,A,B ≃ Γ,B,A $
]
#proof[$Γ,x:A,y:B ⊢ (id_Γ,y,x) : (Γ,B,A)$.]

#lesson("Tears")[If weakening is not an inclusion, the above will be very painful to write down!
For instance, the context expression
$ Γ,x:A,y:B $
does not make sense,
because to extend the context $Γ,A$ with $B$, we need $Γ,A ⊢ B$, as opposed to what we have, which is $Γ ⊢ B$.

So, we need to apply a weakening to get $Γ,A ⊢ B[π_A]$,
and the context is actually $Γ,A,B[π_A]$, and we need to construct the $σ$ in
$ Γ,A,B[π_A] ⊢ σ : Γ,B,A[π_B] $
We begin with weaekning $id_Γ$ into the context, and it's
$ Γ,x:A,y:B[π_A] ⊢ id_Γ [π_A][π_B[π_A]] : Γ $
and we need to append $x$ and $y$ to the end of it, which is even worse.]

== Conclusion

In this chapter, we have postulated the basic structures needed for a well-behaved _substitution calculus_, aka a _dependent type theory_,
which will be used as the foundational framework for the rest of the development.

Importantly, we have shown weakening to be an inclusion.

As a side remark, an alternative to presuppositions @def:presup is to use rules like these:
$ (Γ ⊢ a : A)/(Γ ⊢ A) $
It is up to preference and formalism to choose between the two styles.
We use presuppositions to avoid proving a reason to use the above style.

= Structures I <sec:strut-1>

The goal of this chapter is to defined some simple strucures inside dependent type theories.

We assume readers to know some less formal terminologies, such as introduction rules, elimination rules, term formers, $β$-rules, $η$-laws, etc., which are common in type theory literature.

== Nullary connectives

// Terminal object
#definition("Unit")[
We say a type theory has a _unit type_ if it has the following constructions:

+ _Formation_: $ · ⊢ top $
+ _Introduction_: $ · ⊢ ★ : top $

such that the following rules hold:

+ The fact that the formation of unit type is preserved by substitution:
  $ Γ ⊢ top[σ] ≡ top $
+ The $η$-law: $ (Γ ⊢ a : top)/(Γ ⊢ a ≡ ★ : top) $
] <def:rule:unit>

#lemma[The introduction of unit type is preserved by substitution:
$ Γ ⊢ ★[σ] ≡ ★ : top $] <lem:subst:unit>
#proof[Because $Γ ⊢ ★[σ] : top$, and by the $η$-law.]

In any type theory, as long as we can assign $top$ and $★$ to an existing construction, we consider this type theory to have unit type.

#example[
The boolean type cannot be used to define a unit type, as it has two distinct terms, so the $η$-law does not hold.
]
#lemma[
The projection of a unit type, $Γ,x:top ⊢ π_top : Γ$ is a context isomorphism.]
#proof[The inverse is given by the identity substitution extended with the introduction of $top$: $ Γ ⊢ (id_Γ,★) : (Γ,x:top) $]
In fact, this can be used alternatively to define a unit type.

// Initial object
#definition("Empty")[
We say a type theory has _empty type_ if it has the following constructions:

+ _Formation_: $ Γ ⊢ bot $
+ _Elimination_:
  $ (Γ, x:bot ⊢ u: A)/(Γ, x: bot ⊢ elim_bot (x) : A)
  $

such that the following rules hold:

+ The fact that empty is preserved by substitution:
  $ Γ ⊢ bot[σ] ≡ bot $
+ The $η$-law:
  $ (Γ, x:bot ⊢ u: A)/(Γ, x: bot ⊢ u ≡ elim_bot (x) : A)
  $
]

The $η$-law of the empty type says _any term_ in a context with a $bot$ in it is equivalent to $elim_bot (x)$.

Similarly we can state a theorem similar to @lem:subst:unit:
#lemma[The elimination of empty type is preserved by substitution:
$ (Δ,x:bot ⊢ a:A #h(2em) Γ ⊢ σ : Δ #h(2em) σ' := (σ,x slash x))/
  (Γ,x:bot ⊢ a[σ'] ≡ elim_bot (x) : A[σ']) $] <lem_subst_empty>
#proof[So by typing of the extended substitution object we know $ Γ,x:bot ⊢ σ' : (Δ,x:bot) $
therefore the substitution is well-typed and $ Γ,x:bot ⊢ a[σ'] : A[σ'] $
and by the $η$-law.]

#lemma[For every context extended by $bot$, there is a context isomorphism among each pair of them.

In other words, for all $Γ ⊢$ and $Δ ⊢$, we have a context isomorphism between $Γ, x:bot ⊢$ and $Δ, x:bot ⊢$.]
#proof[
The isomorphism $Γ, x:bot ⊢ σ : (Δ,x:bot)$ is given by a list of $elim_bot (x)$,
whose inverse is given alike.
]

Before proceeding further, we briefly describe the intended way to use these definitions.

There might be a type theory that does not directly define a unit type, but as long as it can provide the data and prove the equations needed by @def:rule:unit, we can say it has a unit type, and may start using the rules of unit type in the type theory.

This is a form of _abstraction_, where we care only about how types are intended to be used, not how they are implemented,
and we use the abstracted rules which usually leads to lighter notations, shorter theorems and proofs, more efficient communications, and more general results.

== Product

// Cartesian product
#definition("Product")[
We say a type theory has _product types_ if it has the following constructions:

+  _Formation_:
  $ (Γ⊢A #h(2em) Γ⊢B)/(Γ ⊢ A × B) $
+ _Introduction_:
  $ (Γ ⊢ a:A #h(2em) Γ ⊢ b:B)/(Γ ⊢ ⟨a, b⟩ : A × B) $
+ _Elimination_:
  $ (Γ ⊢ p : A × B)/(Γ ⊢ p.1 : A)
    #h(2em)
    (Γ ⊢ p : A × B)/(Γ ⊢ p.2 : A)
  $

such that the following rules hold:

+ The fact that product is preserved by substitution:
  $ Γ ⊢ (A × B)[σ] ≡ A[σ] × B[σ] $
+  The fact that projections are preserved by substitution:
  $ Γ ⊢ p.1[σ] ≡ p[σ].1 : A \
    Γ ⊢ p.2[σ] ≡ p[σ].2 : B $
+ The $β$-rules:
  $ (Γ ⊢ a:A #h(2em) Γ ⊢ b:B)/(Γ ⊢ ⟨a,b⟩.1 ≡ a : A) \
    (Γ ⊢ a:A #h(2em) Γ ⊢ b:B)/(Γ ⊢ ⟨a,b⟩.2 ≡ b : B)
  $
+ The $η$-law:
  $ (Γ ⊢ p : A × B)/(Γ ⊢ p ≡ ⟨p.1, p.2⟩ : A × B)
  $
] <def:rule:product>

#lemma("Product extensionality")[
The following rule is derivable:
$ (Γ ⊢ a.1 ≡ b.1 : A #h(2em) Γ ⊢ a.2 ≡ b.2 : B)/
  (Γ ⊢ a ≡ b : A × B)
  $
] <lem:product:ext>
#proof[By $η$-law, what we need to show is equivalently $⟨a.1, a.2⟩ ≡ ⟨b.1, b.2⟩$ and by congruence of equality.]

// Beck--Chevalley condition
#lemma[The introduction of product type is preserved by substitution:
$ Γ ⊢ ⟨a,b⟩[σ] ≡ ⟨a[σ], b[σ]⟩ : A[σ] × B[σ] $] <lem_subst_product>
#proof[
Let $u := ⟨a,b⟩[σ]$. By @lem:product:ext, the goal is equivalently $u.1 ≡ a[σ]$ and $u.2 ≡ b[σ]$.

Since projection is preserved by substitution, we have $(⟨a,b⟩[σ]).1 ≡ (⟨a,b⟩.1)[σ] ≡ a[σ]$, hence $u.1 ≡ a[σ]$, likewise $u.2 ≡ b[σ]$.
]

== Extensional equality

Before diving into more complicated dependently-typed structures, we first introduce a very simple type -- the extensional equality type.

// Equalizers
#definition("Equality")[
We say a type theory has _extensional equality type_ if it has the following constructions:

+ _Formation_:
  $ (Γ ⊢ A #h(2em) Γ ⊢ a:A #h(2em) Γ ⊢ b:A)/
    (Γ ⊢ a =_A b) $
+ _Introduction_:
  $ Γ ⊢ refl_a : a =_A a $

such that the following rules hold:

+ The fact that equality type is preserved by substitution:
  $ Γ ⊢ (a =_A b)[σ] ≡ (a[σ] =_(A[σ]) b[σ]) $
+ The _elimination rule_, also known as _equality reflection_:
  $ (Γ ⊢ p : a =_A b)/(Γ ⊢ a ≡ b : A) $
+ The $η$-law:
  $ Γ ⊢ (p ≡ refl_a) : (a =_A a) $
]

Before stating any properties of extensional equality, observe that in the $η$-law, we do not have a premise $Γ ⊢ p : a =_A b$.
This is because we have _presuppositions_ (@def:presup), implying that this is already assumed when we _state_ the conclusion.

#lemma("Uniqueness")[The following judgment is _derivable_:
$ (Γ ⊢ p : a =_A b #h(2em) Γ ⊢ q : a =_A b)/
  (Γ ⊢ p ≡ q : a =_A b)
  $] <lem:refl:uniqueness>
#proof[
By elimination of equality, we know $Γ ⊢ a ≡ b : A$, hence it suffice to show:
$ Γ ⊢ p ≡ q : a =_A a $
By $η$-law, both $p$ and $q$ are equal to $refl_a$.
]

#lemma[Having _extensional equality type_ and any closed term $· ⊢ a:A$ implies having a _unit type_.]
#proof[Let $top := (a =_A a)$ and $★ := refl_a$.]

== Conclusion

In this chapter, we have defined some simply-typed structures inside dependent type theories, including unit type, empty type, product type, and extensional equality type.

In the next chapter, we will seek to generalize some of these structures into a more general construction.

= Compilers

The goal of this chapter is to defined well-typed translations between type theories, aka compilers.

Before talking about translations between type theories,
we first need to make it explicit that what data give rise to a type theory, and then we define how to translate between them.

== Conventions

We consider a type theory to be a substitution calculus (@sec:subst-calculus) plus a set of postulated rules,
denoted using bold font, e.g. $bold(A), bold(B)$, or $bold("TT")$.

In the presence of multiple type theories, we write $Γ ⊢^bold(A) ...$ to mean that this judgment happens in type theory $bold(A)$.

Recall in last chapter we have introduced a couple of _structures_ of type theories, defined to be having some data and the ability to derive some rules.
When postulating rules, we might just say "$bold(A)$ has product type (@def:rule:product)" to say that we are postulating all the rules needed by product type in $bold(A)$.

The following are some example definitions of type theories:

#example[
- The empty type theory $bold(0)$ has the empty set of postulated rules.
- The unit type theory $bold(1)$ has a unit type.
- Alternatively, another unit type theory has a unit type and product types.
] <ex:empty:unit:fp>
#lemma[In the empty type theory, there is only one context -- the empty one.]
#lemma[In the unit type theory, all contexts except the empty one are isomorphic.]

== Translations

#definition("Compiler")[
A _compiler_ from type theory $bold(A)$ to type theory $bold(B)$, denoted $bold(F):bold(A) → bold(B)$, consists of the following data:

+ A context $Δ$ in $bold(B)$, which we map the empty context in $bold(A)$ to,
+ A pair of functions, called _translations_, both denoted $[| - |]_bold(F)$,
  i.e. for input $A$, it produces output $[| A |]_bold(F)$, maps the types and terms from $bold(A)$ to $bold(B)$.
3. In addition to that, we define $[| Γ |]$ to be iteratively translating the types inside $Γ$ and push them onto $Δ$ -- the translation of the empty context;

such that:

+ For $Γ ⊢^bold(A) A$, the judgment $[| Γ |]_bold(F) ⊢^bold(B) [| A |]_bold(F)$ must be derivable,
+ For $Γ ⊢^bold(A) t : A$, the judgment $[| Γ |]_bold(F) ⊢^bold(B) [| t |]_bold(F) : [| A |]_bold(F)$ must be derivable,
+ If $Γ ⊢^bold(A) A ≡ B$ is derivable, then $[| Γ |]_bold(F) ⊢^bold(B) [| A |]_bold(F) ≡ [| B |]_bold(F)$ is derivable,
+ If $Γ ⊢^bold(A) t ≡ u : A$ is derivable, then $[| Γ |]_bold(F) ⊢^bold(B) [| t |]_bold(F) ≡ [| u |]_bold(F) : [| A |]_bold(F)$ is derivable.
] <def:compiler>

By default, we assume the empty context is translated into the empty context.

When there is only one compiler in the context, we might omit the subscript $bold(F)$.

Observe that presuppositions commute with compilations:

#align(center)[#diagram(cell-size: 15mm, $
  Γ ⊢^bold(A) t: A
    edge("rr", #[presupposes])
    edge("d", [| - |], ->)
    && Γ ⊢^bold(A) A
    edge("d", [| - |], ->) \
  [| Γ |] ⊢^bold(B) [| t |] : [| A |]
    edge("rr", #[presupposes])
    && [| Γ |] ⊢^bold(B) [| A |]
$)]

So, when translating the rules, we do not have to do additional work to ensure that the presuppositions are satisfied.

#example[
For every type theory $bold(A)$, there exists a compiler from $bold(A)$ to the unit type theory $bold(1)$ (@ex:empty:unit:fp), by compiling all types and terms as the unit type and its introduction rule.
]
#example[
For every type theory $bold(A)$, there exists a compiler from the empty type theory $bold(0)$ to $bold(A)$, because there is nothing to compile.
]

Normally, the rules term and type formers are always postulated, not proved to be admissible,
since we have in mind that typing derivations are in correspondence with proof terms, a canonical representation of its _derivation_ -- directly indicates the existence of a derivation.

In the definition of a compiler, we require that the translated judgments are derivable,
not admissible, and the rationale is due to the following construction we wish to be well-defined:

#construction("Composition")[
If $bold(F):bold(A) → bold(B)$ and $bold(G):bold(B) → bold(C)$ are compilers,
then the _composition_ of them, denoted $bold(G) ∘ bold(F):bold(A) → bold(C)$, is a compiler,
defined as follows:

1. For $Γ ⊢^bold(A) A$, define $[| A |]_(bold(G) ∘ bold(F)) = [| [| A |]_bold(F) |]_bold(G)$,
2. For $Γ ⊢^bold(A) t : A$, define $[| t |]_(bold(G) ∘ bold(F)) = [| [| t |]_bold(F) |]_bold(G)$.

The judgmental equalities hold immediately.
]

If we only require the judgmental equalities to be admissible, they wouldn't be further preserved under translation.

#construction("Identity")[
For every type theory $bold(A)$, there exists an _identity compiler_ $id_bold(A) :bold(A) → bold(A)$
such that $[| A |]_id_bold(A) = A$ and $[| t |]_id_bold(A) = t$.]
The use of the keyword $id$ is intentional not bold to be consistent with other identities.

Then, it is tempting to state the unital and associativity laws for compilers,
but to do so we first need a notion of equality between compilers,
which is roughly that they send the same types and terms to the same types and terms.

However, this is not immediately easy, because we care about using types abstractly,
not caring how they are implemented,
so for instance if two compilers are translating something using a unit type,
one uses a distinguished unit type and the other uses a unit type implemented by some other types,
we still consider them to be the same.

== Equivalences

To start, we need to specify the equivalence between $Γ⊢A$ and $Γ⊢B$,
which we intend to do by defining a type-theoretic bijection between their terms.

#definition("Type isomorphism")[
For types $Γ⊢A$ and $Γ⊢B$, a _type isomorphism_ (or _isomorphism_ for short) between them is a pair of terms $Γ,x:A ⊢ b:B$ and $Γ,x:B ⊢ a:A$ such that the following equations are derivable:
$ Γ,x:A ⊢ x ≡ a[b slash x] : A \
  Γ,x:B ⊢ x ≡ b[a slash x] : B $
We denote isomorphic type as a judgment $Γ⊢A ≃ B$.
]

We wish isomorphic types to _behave_ the same in type theory.

Then, we can talk about the equivalence between compilers:

#definition("Equivalent compilers")[
Two compilers $bold(F):bold(A) → bold(B)$ and $bold(G):bold(A) → bold(B)$ are _equivalent_ if for every type $Γ ⊢^bold(A) A$, we have:

+ a context isomorphism $[| Γ |]_bold(F) ⊢ σ : [| Γ |]_bold(G)$,
+ a type isomorphism $[| Γ |]_bold(F) ⊢ [| A |]_bold(F) ≃ [| A |]_bold(G) [σ]$.

We denote equivalent compilers as $bold(F) ≃ bold(G)$.]

#lesson[It is common that instances of a type are usually infinite,
and in that case they are always countable,
as the terms we an write down are essentially _abstract syntax trees_, and trees are countable.

However, there will still be infinite types that are not isomorphic,
since the definition of type isomorphism is an _internal_ isomorphism,
i.e. the isomorphism needs to be _inside_ the type theory.]

Then, we can define the desired unital and associativity laws for compilers:

#lemma[For compiler $bold(F):bold(A) → bold(B)$, we have:
$ (bold(F) ∘ id_bold(A)) ≃ (id_bold(B) ∘ bold(F)) ≃ bold(F) $]
#lemma[For compilers $bold(F):bold(A) → bold(B)$, $bold(G):bold(B) → bold(C)$, and $bold(H):bold(C) → bold(D)$, we have:
$ bold(H) ∘ (bold(G) ∘ bold(F)) ≃ (bold(H) ∘ bold(G)) ∘ bold(F) $]

We also need to establish the equivalence between types theories,
and to do so we need to consider the following:

+ We wish the equivalence to be weak:
  using different implementations of an "abstract" type should not affect the equivalence,
+ If we translate $Γ⊢^bold(A) A$ into $Γ' ⊢^bold(B) A'$, we wish the terms to be translated so that:
  + Different terms get translated into different terms,
  + Every term of $A'$ is the translation of some term of $A$.

Putting all of these conditions together, we can form a sensible notion of equivalence between type theories.

// Essentially surjective
#definition("Surjective")[We say a compiler $bold(F):bold(A) → bold(B)$ to be _surjective_
if for every type $Γ' ⊢^bold(B) B$ there exists a type $Γ ⊢^bold(A) A$ such that:
+ there exists a context isomorphism $Γ' ⊢ σ : [| Γ |]_bold(F)$,
+ $Γ' ⊢ B ≃ [| A |]_bold(F)[σ]$.]

// Fully faithful
#definition("Injective")[Consider a compiler $bold(F):bold(A) → bold(B)$ and a type $Γ ⊢^bold(A) A$.
We say $bold(F)$ to be:

+ _full_ if for every $[| Γ |] ⊢^bold(B) u : [| A |]$,
  there exists $Γ ⊢^bold(A) v : A$ such that $[| Γ |] ⊢^bold(B) u ≡ [| v |] : [| A |]$,
+ _faithful_ if $[| Γ |] ⊢^bold(B) [| u |] ≡ [| v |] : [| A |]$ implies $Γ ⊢^bold(A) u ≡ v : A$.

A compiler is _injective_ if it is both full and faithful.]

#definition("Equivalence")[We say a compiler to be an equivalence between type theories if it is surjective and injective.]

== Conclusion

In this chapter, we defined the notion of a compiler between type theories, which is a sensible _structure-preserving_ map between them, as it preserves the derivability of judgments.

Then, we described a couple of properties of compilers, and used them to define equivalences between type theories.

= Structures, revisited

The goal of this chapter is to revisit the structures defined in @sec:strut-1 with an eye on generalization.

We start the section by a reflection on the definition of "having a unit type" (@def:rule:unit).
For a type theory to have a unit type, the following needs to be true:

For every context $Γ$,
+ there is a type $Γ ⊢ top$,
+ there is a term $Γ ⊢ ★ : top$
  such that every term of this type is equal to it,
+ and this whole thing is preserved by substitution.

For product types, we can rephrase its definition in a similar way,
but with the presence of rule premises, they are more complicated:

For every context $Γ$ and types $Γ ⊢ A$ and $Γ ⊢ B$,
+ there is a type $Γ ⊢ A × B$,
+ for every pair of terms $Γ ⊢ t : A$ and $Γ ⊢ u : B$, there is a term $Γ ⊢ ⟨t, u⟩ : A × B$
  such that every term of this type can be written as such a pair,
+ and this whole thing is preserved by substitution.

Note that the fact that all terms can be written as such a pair is known as all terms _factor through_ the introduction rule.
Similarly for the empty type, all terms in contexts where $bot$ is present _factor through_ the elimination rule.

There seems to be a lot of things in common:

For every context $Γ$ and types $Γ ⊢ 🤔$,
+ there is a type $Γ ⊢ ✨$,
+ for every tuple of terms $Γ ⊢ ... : 🤔$, there is a term $Γ ⊢ ... : ✨$
  such that every term of this type factor through its introduction,
+ and this whole thing is preserved by substitution.

Now, the real question arise: can we generalize this and how do we do that?

== Raw structures

We start by thinking about products.
Given any $Γ⊢A$ and $Γ⊢B$, we may rephrase the introduction of product $A×B$ as having another type $Γ⊢X$ with two _pseudo-projections_:
$ Γ,x:X ⊢ a: A #h(2em) Γ,x:X ⊢ b: B $
which gives me back the original $A$ and $B$.
This motivates the following definition.

// Cones for products
#definition("Raw product")[
Given any $Γ⊢A$ and $Γ⊢B$. A _raw product_ consists of the following data:
+ A type $Γ⊢X$,
+ Two terms $Γ,x:X ⊢ a: A$ and $Γ,x:X ⊢ b: B$.
We denote a raw product as $(X, a, b)$.
]

Then, the product $A×B$ is something we can always use these pieces of information to introduce an instance with, like this:
$ Γ,x:X ⊢ ⟨a,b⟩ : A×B $
Also note that the product $A×B$ can also be used to make a "raw product", namely $(A×B, x.1, x.2)$.
The special feature of this legitimate product is that it has an introduction rule that transforms any raw product into it.

Now, we can redefine the product without assuming its pre-existing rules.

#definition("Product")[
The product $(A×B,x.1,x.2)$ is a raw product such that
for every other raw product $(X,a,b)$, there exists a _unique_ term, called the _constructor_:
$ Γ, x:X ⊢ h : A×B $
such that:
$ Γ, x:X ⊢ a ≡ h.1 : A \
  Γ, x:X ⊢ b ≡ h.2 : B
  $
where $h.1$ is the result of the substitution $x.1 [h slash x]$, and similarly for $h.2$.
] <def:ct:product>
The idea is that constructing a term of type $A×B$ must go through its introduction rule,

We can diagramize the conditions in @def:ct:product as a commutative diagram.
In context $Γ$, we have:
#align(center)[#diagram(cell-size: 15mm, $
  &X cedge("lb", a, ->)
     cedge("rb", b, ->)
     cedge("d", h, "-->")
   & \
  A &A×B cedge("l", .1, ->)
      cedge("r", .2, ->)
  & B
$)]

This is rather like _characterizing_ the product type, instead of _defining_ it.

Now, it is tempting to define another type in a similar vibe.
We start by trying the unit type.

#definition("Raw unit")[
A _raw unit_ consists of the following data:
+ A type $Γ⊢X$,
+ A term $Γ⊢u: X$.
We denote a raw unit as $(X, u)$.
]

Then $(top, ★)$ is an instance of such a raw unit,
and we can characterize the unit type as follows:

#definition("Unit")[
The unit type is a raw unit such that
for every other raw unit $(X,u)$, there exists a _unique_ term, called the _constructor_:
$ Γ ⊢ h : top $
such that:
$ Γ ⊢ u ≡ h : top $
] <def:ct:unit>

It is clear that this coincides with the original definition of the unit type,
where $h$ is just another name for $★$!

== Limit of Compilers

Now, we further generalize the idea of raw structures.
The data in a raw product in type theory $bold(A)$ can be represented as a _cone_,
which is defined below.

#definition("Schema of a product")[
Consider a dependent type theory $bold(D)$ with the following rules:
$ ·⊢A #h(2em) ·⊢B $
The _schema_ of a product in type theory $bold(A)$ is a compiler $bold(F) : bold(D) → bold(A)$.
] <def:schema:product>
Essentially, a schema _chooses_ two types $Γ⊢[| A |]_bold(F)$ and $Γ⊢[| B |]_bold(F)$
in $bold(A)$ for the base context $Γ=[| · |]_bold(F)$.

#definition("Schema of a unit")[
The _schema_ of a unit in type theory $bold(A)$ is a compiler $bold(F) : bold(0) → bold(A)$,
where $bold(0)$ is the empty type theory.
] <def:schema:unit>

#definition("Cone")[
A _cone_ of a schema $bold(F) : bold(D) → bold(A)$ consists of the following data,
where we denote the base context as $Γ=[| · |]_bold(F)$:
+ A type $Γ⊢X$,
+ for every type $Δ⊢A$ in $bold(D)$,
  a substitution $Γ,x:X ⊢ a_A : [| Δ,A |]_bold(F)$,
+ such that the diagram of all $a_A$ and the terms interpreted by $bold(F)$ commutes.
We denote a cone as $Cone(bold(F), Γ⊢X)$, and refer to the diagram mentioned above
as the diagram of this cone.
]
In the above two cases, $Δ$ is always $·$, so the substitution $a_A$ is really just a term.

A _cone_ of the schema in @def:schema:product corresponds to the following diagram:

#align(center)[#diagram(cell-size: 15mm, $
  [| A |] &X cedge("l", x.1, ->)
     cedge("r", x.2, ->)
   & [| B |]
  $)]
Since there is no directed paths that share the same source and target,
the diagram always commutes.
Usually, there will be some term in the image of $bold(F)$,
and in those cases, we will have a nontrivial commutative diagram.

A cone of the schema in @def:schema:unit is just a type $Γ⊢X$.

With the notion of cones, we can define the notion of _limits_,
which should coincide to the original definition of the types (in our case, products and the unit type):

#definition("Limit")[
The _limit_ of the cones of a schema $bold(F) : bold(D) → bold(A)$
is a cone $Cone(bold(F), Γ⊢X)$ such that for every other cone
from the same context $Cone(bold(F), Γ⊢A)$, there is a unique term:
$ Γ,x:A ⊢ h: X $
such that the diagram of both cones and $h$ commutes.
] <def:limit>

Now, let us check that a product is the limit of the schema in @def:schema:product.
A cone for the schema consists of the following data:
+ A type $Γ⊢X$ (where $Γ$ is the base context),
+ For $Γ⊢A$, a term $Γ,x:X ⊢ a_A : A$ (we write $·,A$ as $A$ for simplicity),
+ For $Γ⊢B$, a term $Γ,x:X ⊢ b_B : B$.

The limit of these cones matches precisely with @def:ct:product.
Similarly, a unit type is the limit of the schema in @def:schema:unit,
and we leave the construction as an exercise.

Here is another fun fact: the extensional equality is also a limit!
Let's look at the following schema:

TODO
