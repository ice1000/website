#import "config.typ": *
#show: dtt.with(title: "DTT")

= Introduction

The goal of this chapter is to defined a _substitution calculus_, which a dependent type theory with a well-behaved substitution operation.

= Judgments

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
] <def_presup>

// For expert readers: unless explicitly stated otherwise, the type theory we consider will be structural type theories without modalities or type universes -- so that all type formers are well-behaved and simple.

#definition[We assume judgmental equality to be _reflexive_:
$ Γ ⊢ A ≡ A #h(2em) Γ ⊢ a ≡ a : A $
] <def_refl_jeq>

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
  which holds by @def_refl_jeq. The one for terms is similar.
- Transitivity: $Γ ⊢ A ≡ B$, so we can replace $B$ with $A$ so the other premise becomes $Γ ⊢ A ≡ C$,
  which is equal to the goal.
]

#corollary[
Typing of terms is up to judgmental equality of types:
$ (Γ ⊢ A ≡ B #h(2em) Γ ⊢ a:B)/(Γ ⊢ a:A) $
] <def_typing_jeq>
#proof[$Γ ⊢ A ≡ B$ so we can replace $B$ with $A$ in the premise, which makes it equal to the goal.]

Furthermore, we assume all the congruence rules (i.e. all functions are pure) for the equality judgments, which are omitted everywhere for brevity.

= Contexts and Substitutions

// Context comprehension
#definition("Context")[
A well formed context is inductively generated by the following rules:

$ (·) ⊢ #h(2em) (Γ⊢A)/(Γ,x:A⊢) $
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

#definition("Substitution object")[
A substitution object is inductively generated by the following rules:

$ Γ ⊢ (·) : (·) $
$ (Γ⊢σ:Δ #h(2em) Γ⊢A #h(2em) Γ⊢a:A[σ])/(Γ⊢(σ,a slash x):(Δ,x:A)) $
When the $x$ in $(σ,a slash x)$ is clear from the context, we may omit it, and simply write $(σ,a)$.
]

So, contexts are telescopic lists of types, and substitutions are telescopic list of terms which can be used to substitute variables.

For equality of substitutions, we intend to equate them according to their actions. In other words, two substitutions are equal if they act the same way on types and terms.
#definition("Substitution extensionality")[
If for every $Γ ⊢ A$, $Γ ⊢ A[σ] ≡ A[γ]$, and for every $Γ ⊢ a : A$, $Γ ⊢ a[σ] ≡ a[γ]$, then:
$ Γ ⊢ σ ≡ γ : Δ $
] <def_subst_ext>

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
] <cons_id_subst>

#lemma[Idenity substitution actions are identity functions:
$ Γ ⊢ A[id_Γ] ≡ A #h(2em) Γ ⊢ a[id_Γ] ≡ a : A $]

// Composition of morphisms
#construction("Composition of substitutions")[
For any substitution objects $Γ ⊢ σ : Δ$ and $Δ ⊢ γ : Θ$, we denote $Γ ⊢ (γ∘σ) : Θ$ to be the substitution object formed by induction on $γ$:

+ $γ = (·)$, which implies $Θ = (·)$, we define $(·∘σ) = σ$.
+ $γ = (γ',a)$, which implies $Θ = (Θ',x:A)$, we define $((γ',a)∘σ) = ((γ'∘σ),a[σ])$.
]

#lemma[Composition of substitutions is associative: $ (γ∘σ)∘ρ ≡ γ∘(σ∘ρ) $]
#lemma[Composition of substitutions is unital: $ (id∘σ) ≡ σ #h(3em) (σ∘id) ≡ σ $]
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

#lemma("Weakening")[
The substitution action induced by any projection is an inclusion:
$ (Γ⊢A #h(2em) Γ⊢B)/(Γ,x:A⊢B[π_A] ≡ B) #h(2em)
  (Γ⊢b:B)/(Γ,x:A⊢b[π_A]≡b : B)
 $
]

If weakening is an inclusion, the variable rule becomes very easy to write down,
we can simply say:
$ Γ ⊢ x : A $
if $A$ is not at the end of the context and weakening is not an inclusion,
we would have to write:
$ Γ ⊢ x : A[π_B_1][π_B_2]... $
where $π_B_1,π_B_2,...$ are the projections that delete the types before $A$.

= Conclusion

In this chapter, we have postulated the basic structures needed for a well-behaved _substitution calculus_, aka a _dependent type theory_,
which will be used as the foundational framework for the rest of the development.

Importantly, we have shown weakening to be an inclusion.

As a side remark, an alternative to presuppositions @def_presup is to use rules like these:
$ (Γ ⊢ a : A)/(Γ ⊢ A) $
It is up to preference and formalism to choose between the two styles.
We use presuppositions to avoid proving a reason to use the above style.
