#import "config.typ": *
#import "/book.typ": book-page
#show: thmrules.with(qed-symbol: $square$)
#show: book-page.with(title: "Inside structures")

#show math.equation: it => {
  show "∈": math.scripts
  it
}

= Dependent Theory of Types

This is a series of extremely syntax-minded development on some meta-level dependent type theory,
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
+ $Γ ⊢ σ ≡ τ : Δ$ means $σ$ and $τ$ are equal substitution objects from $Γ$ to $Δ$.
]

In fact, we don't necessarily need $Γ ⊢ A$, $Γ ⊢ a : A$, and $Γ ⊢ σ : Δ$, as they can be seen as reflexive case of the equality judgments, but we keep them regardless for better readability.

For empty contexts and substitutions, we overload the symbol $·$ to represent both of them, usually wrapped in parentheses.

// A Bob Harper thing
#definition("Presuppositions")[
The judgments come with _presuppositions_ that are always assumed:

+ $Γ ⊢ A$ presupposes $Γ ⊢$.
+ $Γ ⊢ A ≡ B$ presupposes $Γ ⊢ A$ and $Γ ⊢ B$.
+ $Γ ⊢ a : A$ presupposes $Γ ⊢ A$.
+ $Γ ⊢ a ≡ b : A$ presupposes $Γ ⊢ a : A$ and $Γ ⊢ b : A$.
+ $Γ ⊢ σ : Δ$ presupposes $Γ ⊢$ and $Δ ⊢$.
+ $Γ ⊢ σ ≡ τ : Δ$ presupposes $Γ ⊢ σ : Δ$ and $Γ ⊢ τ : Δ$.
]

For expert readers: unless explicitly stated otherwise, the type theory we consider will be structural type theories without modalities or type universes -- so that all type formers are well-behaved and simple.

== Contexts and Substitutions

// Context comprehension
#definition("Context")[
A well formed context is inductively generated by the following rules:

$ (·) ⊢ #h(2em) (Γ⊢A)/(Γ,x:A⊢) $
]

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

$ Γ ⊢ (·) : (·) #h(2em) (Γ⊢σ:Δ #h(2em) Γ⊢A #h(2em) Γ⊢a:A[σ])/(Γ⊢(σ,a):(Δ,x:A)) $
]

So, contexts are telescopic lists of types, and substitutions are telescopic list of terms which can be used to substitute variables.

We assume substitution to behave nicely,
which decomposes to the following laws:

// Identity morphism
#definition("Identity substitution")[
For any context $Γ$, we denote $Γ ⊢ id_Γ : Γ$ to be the substitution object satisfying the following rules:

$ (·)⊢id_((·)) : (·) #h(2em) (Γ ⊢ id_Γ : Γ)/(Γ,x:A⊢id_(Γ,x:A) : (Γ,x:A)) $
so that $Γ ⊢ A[id_Γ] ≡ A$ and $Γ ⊢ a[id_Γ] ≡ a$.
]

// Composition of morphisms
#construction("Composition of substitutions")[
For any substitution objects $Γ ⊢ σ : Δ$ and $Δ ⊢ τ : Θ$, we denote $Γ ⊢ (τ;σ) : Θ$ to be the substitution object formed by induction on $τ$:

+ $τ = (·)$, which implies $Θ = (·)$, we define $(·;σ) = σ$.
+ $τ = (τ',a)$, which implies $Θ = (Θ',x:A)$, we define $((τ',a);σ) = ((τ';σ),a[σ])$.
]

#lemma[Composition of substitutions is associative: $ (τ;σ);ρ = τ;(σ;ρ) $]
#lemma[Composition of substitutions commutes with substitution action: $ A[τ;σ] = A[σ][τ] #h(2em) a[τ;σ] = a[σ][τ] $]
Note that the order is reversed.

// Display maps
#definition("Projection")[
For any type $Γ⊢A$, we denote $Γ,x:A ⊢π_A : Γ$ to be the substitution object such that for every $Γ⊢a:A$, we have:
$ Γ ⊢ (π_A;(id_Γ,a)) ≡ (id_(Γ,x:A)) : Γ $
]
#construction("Weakening")[
We may induce a substitution action by any projection,
which we refer to as _weakening_:
$ (Γ⊢A #h(2em) Γ⊢B)/(Γ,x:A⊢B[π_A]) #h(2em)
  (Γ⊢b:B)/(Γ,x:A⊢b[π_A] : B[π_A])
 $
]

#definition("Containment")[
We introduce the judgment $x:A ∈_n Γ$ to be generated by the following rules:

$ x:A ∈_0 (Γ,x:A) #h(2em) (x:A∈_n Γ)/(x:A∈_(n+1)(Γ,y:B)) $
]
#lemma("Non-empty")[If $x:A ∈_n Γ$, then the context $Γ$ is not empty,
therefore if $σ:Γ$, we may decompose it as $(σ',a):Γ$.]

For readers familiar with implementation of type theories, the above two rules correspond to the zero and successor of de Bruijn indices.

#definition("Variable")[
We assume the following rule:
$ (x:A ∈_n Γ)/(Γ ⊢ x:A) $
such that substitution acts on variables as follows:
$ (x:A ∈_0 Γ)/(Γ ⊢ x[σ,a] ≡ a : A[σ]) \
  (x:A ∈_(n+1) (Γ,y:B) #h(2em) Γ ⊢ x[σ] : A')/
  (Γ, y:B ⊢ x[σ,b] ≡ x[π_B;σ]:A'[π_B])
 $
]
