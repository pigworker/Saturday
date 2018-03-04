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
parser and an uglyprinter for this syntax in the engigmatically named [R.hs](src/R.hs)
file.


## Co-de-Bruijn Representation

The essence of co de Bruijn representation is to be explicit about
*thinning*, or *order-preserving embedding* (`OPE`), embedding smaller
scopes into larger scopes. Or, advancing from the root of a term,
thinnings can be seen as expelling unused variables from scope.

The basic machinery can be found in [B.hs](src/B.hs) for backward
lists and bit-twiddling.

In this development, `OPE` is not indexed over source and target
scopes, as I often do in Agda. Rather,

    type OPE = Integer

which is being misused as a representation of bit vectors. The bit at
the little end tells you the fate of the most local variable (1 to
keep it, 0 to throw it away); the next bit left tells you about the
next-to-most-local, and so on. We may safely ignore the 'instructions'
a thinning gives us about variables which aren't in scope, so we must
identify them up to their least *n* significant bits when there are
*n* variables in scope.

Two's complement representation now comes in handy: -1 is the identity
thinning (`oi`), with all bits set; 0 is the empty thinning (`oe`),
discarding all variables. Thinnings are extended by two operations
which decide the fate of some newly bound top variable: successor
(`os`) retains it, and that's double-and-add-one; skipping (`o'`)
discards it, and that's just doubling. Note that `oi` is the fixpoint
of `os` and `oe` the fixpoint of `o'`.

Composition of thinnings is a funny old operation. I write it
*diagrammatically*, so &theta; `<<` &phi; means thinning by
&theta;, then by &phi;, or expelling by &phi; then &theta;, if you
take a rootist view. You can read the bits of &phi; (from the little
end) as instructions for processing &theta; from the little end
to construct the composite: 0 means 'insert 0, retaining &theta;', 1
means 'move the next bit from &theta;'.

We then do a lot of work with the type of *relevant* things

     data Re x = x :^ OPE deriving Show

where *x* `:^` &theta; is intended to store *x*s which are sure to
use all of the variables that &theta; has not thrown away.

The crucial data structure is the *pair relevant*

    type PR s t = (Re s, Re t)

where the key invariant is that the thinnings in each component of the
pair cover the whole of the scope between them: if neither component
want to use a given variable, it should have been expelled earlier.
Given two thinnings, &theta; and &phi;, we can compute the thinnings which
make &theta; `.|.` &phi; a *pushout*, embedding the subscopes selected
by each thinning into their union.

    psh :: OPE -> OPE -> (OPE, OPE)

This construction is exactly what we need to compute relevant pairing:

    pR :: Re s -> Re t -> Re (PR s t)
    pR (s :^ ai) (t :^ bi) = (s :^ ai', t :^ bi') :^ (ai .|. bi) where
      (ai', bi') = psh ai bi

