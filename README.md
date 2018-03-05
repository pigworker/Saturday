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

The operation

    (<?) :: OPE -> Int -> Int

computes the number of variables in the domain of a thinning (or how
may are not expelled), given how many there are in the range. Its
friend

    (<??) :: OPE -> Bwd x -> Bwd x

computes the selection of a snoc-list given by a thinning. Morally,
that extends vectors to a contravariant functor from thinnings to
Set (i.e. an embedding from n to m tells you how to choose n things from m).

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

    (<<) :: OPE -> OPE -> OPE
    ai << (-1) = ai
    ai << 0    = oe
    (-1) << bi = bi
    0    << bi = oe
    ai << bi     = case bout bi of
      (bi, False)  -> o' (ai << bi)
      (bi, True)   -> case bout ai of
        (ai, a) -> (ai << bi) <\ a

    bout :: OPE -> (OPE, Bool)
    bout i = (shiftR i 1, testBit i 0)

    (<\) :: OPE -> Bool -> OPE
    i <\ False  = shiftL i 1
    i <\ True   = shiftL i 1 .|. bit 0

We then do a lot of work with the type of *relevant* things

    data Re t = t :^ OPE deriving Show

where *t* `:^` &theta; is intended to store *t*s which are sure to
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

Constants embed directly, with no variables relevant.
    
    kR :: t -> Re t
    kR t = t :^ oe

A *spine* is a snoc-list made by relevant pairing.

    data Sp x = S0 | SZ (PR (Sp x) x) deriving Show

We may compute a backward list of relevant things from a relevant
spine

    unSp :: Re (Sp x) -> Bwd (Re x)
    unSp (S0 :^ _)           = B0
    unSp (SZ (xz, x) :^ ci)  = unSp (xz ^<< ci) :\ (x ^<< ci)

where the `^<<` operator post-composes a thinning

    (^<<) :: Re t -> OPE -> Re t
    (t :^ ai) ^<< bi = t :^ (ai << bi)

without touching the underlying thing.

Variables are trivial, because by the time you use one, there should
be only one variable in scope.

    xR :: Int -> Re ()
    xR i = () :^ bit i

To construct bindings, we must say *how many* variables are bound,
then immediately, *which* are relevant.

    data Bn t =  (Int, OPE) :\\ t deriving Show

We may then define the simultaneous abstraction:

    (\\) :: Int -> Re t -> Re (Bn t)
    n \\ (t :^ ci) = ((n, bi) :\\ t) :^ ai where (ai, bi) = bouts n ci

where `bouts` *n* is the operation that comes out from under *n*
binders, splitting a thinning into its free and bound components.

    bouts :: Int -> OPE -> (OPE, OPE)
    bouts n i = (shiftR i n, i .&. (2 ^ n - 1))

With constants and pairing, abstraction and usage, we have all the
tools to build syntax trees.


## Abstract Syntax

The file [Tm.hs](src/Tm.hs) contains the definition of the abstract
syntax, and pretty much the rest of the workings (so it is sure to
get split in due course).

Constructions are as follows,

    data TC
      = A A           -- atom                                 a
      | V             -- void                                 ()
      | P (PR TC TC)  -- pair                                 (car, cdr)
      | I TC          -- inductive wrapping                   [stuff..]
      | L (Bn TC)     -- lambda, never nullary, never nested  \ x t
      | E TE          -- elimination                          {elim..}
      deriving Show

defined mutually with eliminations

    data TE
      = X (PR () (Sp (Bn TE)))   -- use of (meta)variable, with spine of parameters
      | Z (PR TE TC)             -- zapping something with an eliminator
      | T (PR TC TC)             -- type annotation   {term : Type}
      deriving Show

The next step is to define the extraction of relevant terms from raw
terms. Now, in Constructive Engine style, that ought to be done at the
same time as typechecking. That's to say, we should represent only
trusted terms in the abstract syntax. But I'm a wrong'un in a hurry.
All that's needed to fuel the construction is the names (and parameter
info) for the (meta)variables in scope.

I should say something about metavariables and spines. The *object*
variables of the calculus, bound with `L`, are usable as eliminations
with an empty spine. However, this syntax also allows us to invoke
*meta*variables, which live at the global end of scope and will be
bound by the *proof state*. Metavariables can be hereditarily
parametrised, and their parameters must be instantiated at usage
sites, which is why variables take a spine.

Making object variables the boring special case of metavariables means
that we may use the same machinery (*hereditary substitution*) for
hole-filling as well as for yer basic &beta;-reduction.


## Simultaneous Hereditary Substitution

In [B.hs](src/B.hs), I define a notion of
morphism from a source scope to a target scope, keeping track of

* which source variables are being overwritten
* which target terms are overwriting them
* how to embed the left variables into the target scope

But not necessarily in that order (as I keep the left variables to the left):

    data Morph t = Morph {left :: OPE, write :: OPE, images :: Bwd (Re t)}
      deriving Show

Now, we can refine a substitution down to those source variables which
survive a thinning.

    (<%) :: OPE -> Morph t -> Morph t
    bi <% Morph th ps sz = Morph (th0 << th) bi0 (ps0 <?? sz) where
      (bi0, ps0) = pll bi ps
      (_, th0)   = pll bi (complement ps)

Here we make key use of the fact that thinnings have *pullbacks*.

    pll :: OPE -> OPE -> (OPE, OPE)

computes the embedding into two subscopes from their intersection,
which tells you how to thin the variables which remain for thinning
and which substitution images can be thrown away. The `<??` operator
treats a thinning as a selection from a snoc-list.

The other key operation we need on substitutions is to push them
under a binder.

    (%+) :: Morph t -> (Int, OPE) -> Morph t
    Morph th ps sz %+ (n, bi) =
      Morph (bins th n bi) (shiftL ps (bi <? n)) (fmap (wks n) sz)

We're going under `n` binders, so we have `n` new target variables,
and `bi` tells us which of them are actually used in the source term
under the binder. We need to thin all our images by `n`:
    
    wks :: Int -> Re t -> Re t
    wks n (t :^ bi) = t :^ shiftL bi n

We need to left-shift the `write` selector by the number of new source
variables, as none of them is being written. Correspondingly, we need
to extend the thinning for the `left` variables into the target
context with exactly the information from the binder.

    bins :: OPE -> Int -> OPE -> OPE
    bins ai n bi = shiftL ai n .|. (bi .&. (2 ^ n - 1))

What's pleasing is that we've got as far as pushing morphisms under
binders without saying anything about the syntax at all. Unlike de
Bruijn representations, we don't need to go all the way to the leaves
to thin a substitution ready for use under a binder, because the
substitution images carry a thinning at their root.

Now we arrive in [Tm.hs](src/Tm.hs), and we choose substitution images
to be binding forms, allowing metavariable instantiation to abstract
over parameters.

    type HSub = Morph (Bn TE)

I introduce a type class for things which admit hereditary
substitution, mostly to try to make each mistake only once.

    class HSUB t where
      hs, hsGo :: HSub -> t -> Re t
      hs (Morph bi _ B0) t = t :^ bi
      hs sb t = hsGo sb t

Things to note:

* The `t` being substituted should use everything in scope so the
morphism should have no junk in it.
* A substitution does not promise to use all the target variables
available, so the output needs a `Re`.
* Accordingly, we know that if *none* of the variables is being
written, they are all being left, which we do by action at the
root.
* The wrapper `hs` tests for whether a substitution and calls the
worker `hsGo` only if there is work to do.
* Instances should define only `hsGo`. Recursive calls should be to
`hs` if the scope gets smaller, but `hsGo` if it stays the same or
grows under a binder: if we were hunting a free variable before,
we still are, now.
* Although it potentially avoids vast swaths of closed term, we are
still proceeding at a trundle. The notorious *underground*
representation might improve things, allowing us to barrel along a
network of *tubes* (closed one-hole contexts) between the interesting
choice points.

The action is in the `TE` instance, and specifically in the `X` case

    hsGo sb (X (() :^ x, sp :^ ai)) = case x <% sb of
      Morph y _ B0         -> fmap X (pR (() :^ y) (hs (ai <% sb) sp))
      Morph _ _ (_ :\ pv)  -> stan pv (hs (ai <% sb) sp)

where we know that `x` is a singleton thinning, so refining the
substitution by it will tell us pretty directly whether the variable
gets substituted or not. If not, we have just the singleton we need
to build the target. But if it's time to write, we need to turn the
spine of (substituted) parameters into the hereditary substitution
which instantiates the formal parameters if the image.

    stan :: HSUB t => Re (Bn t) -> Re (Sp (Bn TE)) -> Re t
    stan (((n, bi) :\\ t) :^ th) sp =
      hs (Morph th (bins oe (bi <? n) oi) (bi <?? unSp sp)) t

Now we're thinning the *free* variables and substituting the *bound*
variables (having first turned the spine into a snoc-list and selected
only those which are used in the image). Of course, if there are no
parameters (or none are used), then `t` will not be traversed.


## Root Normal Form

I call a type a *Geuvers* type if reducing its expressions to
canonical or neutral is a sound and complete test for whether they are
judgmentally equal to a canonical form. That is, in a Geuvers type,
we don't need to do anything clever to reveal a canonical root node:
we just compute. Typechecking algorithms rely on sorts (types of
types) being Geuvers types.

Because I build syntax out of LISP, I choose to work a little harder
than weak-head-normalization: I keep computing until I reach a binder,
but I don't go under. I call this *root-normalization*. It's (more
than) enough to reveal head type constructors and all their children,
assuming types are Geuvers.

The core recursion is between 

    rnfC :: Cx -> Re TC -> Re TC
    rnfE :: Cx -> Re TE -> (Re TE, Re TC)

where the latter does type reconstruction, which is why both need to
know the *context*. However, `rnfC` does *not* need to know the *type*
of the thing being reduced exactly because we do not go under binders,
so we need never *extend* the context.

Now, there is something funny going on. If we were doing only
&beta;-reduction, we would not even need to do type reconstruction,
because the bidirectional discipline ensures that every &beta;-redex
makes the active type *explicit*: we do not need to reconstruct the
types of neutral terms exactly because they're not going to compute
anyway. However, some type theories (notably, *cubical* type theories)
have reduction rules which eliminate neutral terms to canonical values
when their *types* tell us enough information (e.g., projecting an
*endpoint* from a path whose type specifies the values at the ends).
Type reconstruction for eliminations is not hard, and if we want such
type-directed behaviour, we have to do it to stay Geuvers.


## Type Checking and Synthesis

For constructions, we have

    chk :: Cx        -- context
        -> Re TC     -- type to check, already in rnf
        -> Re TC     -- candidate inhabitant
        -> Maybe ()  -- well, did ya?

and for eliminations

    syn :: Cx              -- context
        -> Re TE           -- elimination for which to synthesize type
        -> Maybe (Re TC)   -- synthesized type in rnf

We have to be careful to enforce the rnf invariants (or else the
typechecker will reject valid things for want of a little elbow
grease). Where we `E`mbed eliminations into constructions, we have
a clearly directed type comparison to do: the type we've got meets
the type we want, so there is an opportunity for subtyping (which I
propose to use for *cumulativity*, at least).

    subtype :: Cx        -- context
            -> Re TC     -- candidate subtype in rnf
            -> Re TC     -- candidate supertype in rnf
            -> Maybe ()  -- well, did ya?

Canonical type constructors have structural rules imposing suitable
co- or contravariant conditions on their children. For stuck
eliminations, we revert to an equality test. We have
type-reconstructing equality for eliminations

    qE :: Cx             -- context
       -> Re TE          -- e the first in rnf
       -> Re TE          -- e the second in rnf
       -> Maybe (Re TC)  -- are they equal with a synthesized type in rnf

and type-directed equality for constructions

    qC :: Cx           -- context
       -> Re TC        -- type in rnf
       -> Re TC        -- t the first in rnf
       -> Re TC        -- t the second in rnf
       -> Maybe ()     -- well, were they?

which allows us to impose &eta;-laws wherever convenient, and
certainly for functions. &eta;-expansion is easy in co-de-Bruijn
syntax because thinning is laughably cheap.

