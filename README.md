# Saturday
being a thing I build on a Saturday


## What is it?

It's a kind of revisionist LISP, with a bidirectional dependent type
system. The implementation uses a *co-de-Bruijn* representation of
terms: that's a nameless representation where variables are thrown out
of scope at the *earliest* moment they're known to be unused (where
*de Bruijn* representations of terms delay observations of non-use to
the leaves of the syntax tree where we decide to use one variable and
thus not the others).

So far, I have a parser, an implementation of beta-reduction, a
type-directed equality, and a typechecker for Pi-types. More will
follow. The implementation of substitution should be good also for
metavariable instantiation in construction by refinement.


## Concrete Syntax

*construction* ::= *atom* | `(` *constructions* `)` |
 `[` *constructions* `]` | `\` *atom* *construction* | `{` *elimination* `}`

*constructions* ::= | *construction* *constructions* | `,`
*construction*

*elimination* ::= *atom* | *elimination* *construction* | `{`
 *construction* `:` *construction* `}`

*atom* ::= (*alpha* | *digit* | *symbol*)+

*alpha* ::= `A` | .. | `Z` | `a` | .. | `z`

*digit* ::= `0` | .. | `9`

*symbol* ::= `_` | `-` | `<` | `=` | `>` | `*` | `'`

Atoms are used both as tags in constructions and as variables in
eliminations. Brackets `[`..`]` mark the unrolling of syntactic
fixpoints, and they typically contain right-nested null-terminated
sequences of pairs, often with an atom at their head. Types, in
particular, take that form. Abstractions, `\` *x* *t*, do not need
parentheses, because they abstract exactly one variable and there
are enough delimiters around to avoid ambiguity.

Function types look like

    [Pi {S} \ s {T {s}}]

Universes look like

    [Type {sort}]

The joy of LISP is that I can add stuff to the language without
changing its concrete syntax. Or rather, the *actual* concrete
syntax is how you make stuff out of the LISP-like components.

There is an
[attoparsec](https://hackage.haskell.org/package/attoparsec-0.13.2.2/docs/Data-Attoparsec-Text.html)
parser for this syntax in the engigmatically named [R.hs](src/R.hs)
file.
