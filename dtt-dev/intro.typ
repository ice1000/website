#import "config.typ": *
#show: dtt.with(title: "DTT")

#let intro-fulltext = [
== Introduction

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
The usual definition of admissibility is that it does not add new theorems to the theory,
but I personally find it too much of a characterization, and is far from something we can easily verify.

In practice, it's most likely the case that admissible rules are proved by case analysis on the premises,
which is usually clearer how to do.
]
#intro-fulltext
