# Proposal: Multimode Agda
J.w.w. Malin Altenmüller, Joris Ceulemans, Lucas Escot, Josselin Poiret

## Intro
At the Agda Implementers' Meeting XXXI, the above people have worked on implementing a modal
type system for polarities (isovariant/parametric/natural/unused, strictly positive, positive,
negative, mixed-variant) for Agda, as a replacement of the current polarity checker for (co)inductive
types. Their code can currently be found at
https://github.com/flupe/agda/tree/polarity

Lots of interesting problems popped up and were discussed. This note intends to discuss
everything that needs to be considered both in future modal extensions of Agda and in the current implementation
(because a couple of things are currently off). This note will keep evolving.

## Rough table of contents

- Mode
   - Annotate judgement (i.e. TCM) with a mode instead of a modality
   - Modes & modules
   - Metamode
- Abstract mode theory interface
- Several orthogonal instances
- Modal module & record fields
- `workOnTypes` / the parametroid modality
- Think about future support for explicit 2-cells
- Principal annotation for functions
- Syntax
   - maybe be principled, eg `pol:++`, `coh:\b`, ...

## Implementing modes

Currently, the judgement (i.e. the TCM) is annotated with a modality. This modality
serves two purposes:

1. It remembers how to access definitions (which can have a modal annotation) so that
   you cannot access e.g. an irrelevant definition in a relevant position. Theoretically,
   this means that it serves as a lazy left devision on the namespace of definitions.
2. For erasure, it remembers what mode we are in.

The annotation should be kept solely for the first purpose.
For the second purpose, we should have a mode annotation instead of a modality annotation.

### Modes and modules

Currently, modules cannot be annotated with a modality.
In multimode type theory, this becomes annoying. (Since unimode type theory is a special case
of multimode type theory, it probably already is annoying.) Indeed, I guess Agda would
start typechecking a file in some fixed starter mode (e.g. `programMode` and not `logicalMode`).
But maybe we want to do a couple of definitions in another mode, so it would be practical to
annotate an entire module.
In Menkar, modal annotations on definitions and modules are really just locks appearing
in the parameter telescopes, so you can put them on anything. I think in Agda
we should at least be able to have a modal annotation which boils down to having a lock
in front of all the parameters.
This means that the first purpose above will become more complicated: the modality
with respect to which we access other definitions, depends on how far outwards
we have to reach through the nested modules that we're currently in. So I guess we need
a list of modalities instead.

### Top-level definitions and the metamode
Josselin fixed a bug in cohesion that allowed using non-flat definitions in flat positions.
This probably breaks a lot of code written using the flat modality. The reason is that
in Agda flat, the following rule
```
Γ |– t : Box-flat T
-------------------
Γ |– unbox t : T
```
is illegal *unless `Γ` is the empty context*. So the following is theoretically ok:
```agda
module M where
  postulate A : Set
  
  @flat A' : Set
  A' = A
```

but the following is not:
```
module M (A : Set) where
  Id : Set
  Id = A
  
  @flat Id' : Set
  Id' = Id
```

Since modalities in Agda do not behave differently depending on whether the context is empty,
they either accept or refute both of the examples. They used to accept both, which is a bug.
(**EDIT:** I think I misunderstood the bug Josselin fixed. In fact, it turns out that w.r.t. cohesion,
modules are entirely see-through w.r.t. their desugaring as top-level definitions, i.e. the telescope
of a module simply gets distributed over its entries and they are type-checked accordingly.)
After Josselin's fix, they now refute both. But I suspect that instances of the first
example are all over people's agda-flat code, so we need to give them a way out.

I think top-level definitions, i.e. definitions (within a module or not) that do not have a single
module parameter, should not be annotated with a modality, but with a mode. These things
are then not considered as defined programs in the context, but as defined derivations in
the metacontext. The above then becomes:

```agda
module M where
  postulate &theonlymode A : Set
  
  &theonlymode A' : Set
  A' = A
```

Perhaps similarly, we should have module parameters annotated with a mode (up until the first
module annotated with a mode). Then a context will consist of:
- A bunch of closed metavariables (in the non-Agda sense) annotated with a mode
- A signpost that says: "As of this point, we're working internal to the type system,
  and we're starting at mode `m`"
- A bunch of variables annotated with a modality whose codomain is `m`

It would be sane to only allow mode-annotated arguments on modules and not on function types.
However, module entries externally look like functions. Actually that's not too bad,
then we just get metafunction metatypes.

This is probably all quite hard to implement, but we can obtain it by freely extending the
mode theory with:
* a new initial mode `meta`, with unique modalities `fromMeta m : meta -> m` to all pre-existing modes `m`,
  - note that initiality implies that `µ º fromMeta m = fromMeta n`,
* each `fromMeta` has a right adjoint `toMeta m : m -> meta`,
  - note that initiality implies that `toMeta m º fromMeta m = id : meta -> meta`
  - note that `boxMeta m = fromMeta m º toMeta m : m -> m` is an idempotent comonad,
    which indicates a metatheoretical dependency.
  - more generally, `viaMeta m n = fromMeta n º toMeta m : m -> n` is the least modality
    `m -> n`. Indeed, we have
    ```
    µ ≥ boxMeta n º µ º boxMeta m
    = boxMeta n º viaMeta m n
    = viaMeta m n
    ```
* pattern-matching should be disallowed under `toMeta m`.

We start at mode `meta`. Instead of annotating a definition/parameter with mode `m`,
we annotate with `toMeta m`. When we enter that position, we left divide the context
by `toMeta m`, which is equivalent to composing with `fromMeta m`. This turns
`id : meta -> meta` into `fromMeta m : meta -> m` and `toMeta n` into `viaMeta m n`.

## Some mode theories

### Quantities

#### Mode theory for erasure and non-erasure

We can view the erasure theory as a mode theory, provided that we do not care about quantities
other than 0 and ω.

The most remarkable aspect of the erasure theory is the (intended!) possibility to write the
following:

```agda
module (A : Set) where
  @0 unerase : @0 A -> A
  unerase a = a
```

What happens internally is that, when we move into an erased subterm, the judgement (i.e. the TCM)
gets annotated with `@0` (as opposed to the original `@ω`).
This annotation makes the language behave differently: it suddenly allows us to use (newly abstracted!)
erased variables in (locally) non-erased positions.
Conversely, non-erased variables are always allowed in erased positions.
Hence, when the judgement is annotated with `@0`, erasure and non-erasure are conflated.

This means that the annotation `@0` on the judgement really puts Agda in a different type-checking
mode. This can be perfectly formalized using modes of MTT.
We will not be able to write verbatim the same thing, but we can morally get the same functionality.

MTT is parametrized by a mode theory, which is a 2-category whose

- objects are called modes
- morphisms are called modalities
- 2-cells are called 2-cells
  For now, we will assume that there is always at most one 2-cell between any two given modalities,
  and that it can be decided whether there is one, i.e. the type of modalities will be an `Ord` instead
  of a category.

I propose the following mode theory for erasure:

```
                               forgetRuntime
                 +-----------------<---------------+
                /                                   \
        logicalMode                ⊥            programMode
                \                                   /
                 +----------------->---------------+
                              trivialRuntime
```

Types in `programMode` (the default mode) can be thought of as equipped with two relations:
equality now and equality at runtime.
For types in `logicalMode`, there is just one relation: equality now, since they will never be run.
The modality `forgetRuntime` forgets the equality relation at runtime.
The modality `trivialRuntime` gets back to two relations by equating everything at runtime.

Disregarding type erasure, there is a straightforward presheaf model of this,
where `logicalMode` is modelled in sets and
`programMode` is modelled in a category known by different names:

- The Sierpiński topos,
- The arrow category of Set,
- Presheaves over the walking arrow.
  
(If you want to model type erasure, you get a problem in `programMode`, and the problem can be
traced down to the impossibility to get the type at runtime if it's been erased. Presheaf
models are intrinsically typed, you know.)

We give a name to one composed modality:

```
erase = trivialRuntime º forgetRuntime : programMode -> programMode
```

The other composition amounts to the identity:

```
forgetRuntime º trivialRuntime = id : logicalMode -> logicalMode
```

The two modalities are adjoint: `forgetRuntime –| trivialRuntime`.
From this, we learn that `erase` is an idempotent monad,
meaning that `id ≤ erase : programMode -> programMode`.

The `unerasure` function is now defined for types coming from `logicalMode`
(I annotate modes using `&`; when combined with a modality annotation,
the given mode is the modality's domain).
We need a modal box type (the following only type-checks for mode theories
where there is no "parametric" modality, see later on):

```agda
data Box-µ (@µ A : Set) : Set where
  box-µ : (@µ a : A) -> Box-µ A
```

```agda
&programMode
module (@trivialRuntime &logicalMode A : Set) where

  &programMode unerase : @erase Box-trivialRuntime A -> Box-trivialRuntime A
  unerase (box-trivialRuntime a) =
    {- a is now in scope with modality erase º trivialRuntime = trivialRuntime -}
    box-trivialRuntime a
```

Another sign that we've done things right is that, at `logicalMode`, there really
is only one endomodality. Above, we saw that when the judgement is annotated with
`@0`, then erasure and non-erasure get conflated.

#### Substructural system for quantities

Quantities currently seem to have been implemented with a substructural system in mind.
When checking a (multiplicative?) term, quantities of subterms should be added.
However, when we write up typing rules to be checked by a type-checker, we have to be
aware of what is input and what is output.
The amount of times a variable can be used, is found in the context. The context of the
conclusion is input, and the content of the premises is output.
So we cannot compute the former by adding the latter.
Instead, the type-checker should
report on the remaining amount of times a variable can be used.
A rule such as function
application should be checked as follows:

```
Γ,  p times x : A |— f : A -> B          >> Γ',  q times x : A
Γ', q times x : A |– a : A               >> Γ'', r times x : A
-------------------------------
Γ,  p times x : A |— f b : B             >> Γ'', r times x : A
```

### Guarded
Currently, `--guarded` gives you a system with exactly one clock.
With modalities, we can easily get a system with ≤1 clock.
The mode theory is then the modal bowling pin (or torpedo in ascii):
```
                               constantly
                 +----------------->---------------+     +-->--+
                /                                   \   /      |
             timeless              ⊥               timeful     | later
                \                                   /   \      |
                 +-----------------<---------------+     +--<--+
                                forever
```
where `forever º constantly = id : timeless -> timeless`
and `always = constantly º forever : timeful -> timeful` is a comonad.

To obtain multiclock type theory, we could take the free (cartesian
category with same terminal object) over this category, but clocks
will be meta-things (e.g. natural numbers).
The tick-based approach to guarded type theory is better suited
to be extended with multiple clocks.

## Abstract mode theory interface

It would be good if there is a general interface that needs to be implement to add a mode theory to Agda.
Here, we discuss the methods in this interface.

* A type of modes
* A type of modalities
* A partial order on modalities
  * In the future, we may instead use a type of 2-cells
* A composition operation on modalities with matching (co)domain
  * Associativity is quickcheckable
* A left division operation `(µ \ —) : Mod p n -> Mod p m` which is left adjoint
  to `(µ º —) : Mod p m -> Mod p n`. This means that either of the following quickcheckable properties
  needs to be satisfied:
  * `forall ρ μ ν . ρ \ μ ≤ ν iff ρ ≤ μ º ν`
  * `forall ρ μ . ρ \ (ρ º μ) ≤ μ` (co-unit) and `forall ρ μ . μ ≤ ρ º (ρ \ μ)` (unit)
* Addition should **not** be part of a general mode theory interface, as it is relevant only to
  substructural theories.
* the identity (a.k.a. unit) modality
  * Unit laws are quickcheckable
* the default modality for binders
* related to module entries and record fields:
  * the default modality for module entries and record fields
  * `hasLeftAdjoint`: a function that computes whether a modality has an internal left adjoint.
    A very smart standard implementation with proof-in-comments is presently present in the agda code base.
    If a modality `µ` has an internal left adjoint, then it can be computed as `µ \ id`.
    In general, `µ \ id` is the universal (minimal) **upper** approximation of the left adjoint, in the sense that we have the unit law
    ```
    id ≤ µ º (µ \ id)
    ```
  * `getApproximateLeftAdjoint`: a function that computes whether a modality `µ` has a **lower** approximation
    of the left adjoint, i.e. a modality `κ` such that we have the co-unit `κ \ µ ≤ id`.
    This inequality may have multiple solutions. In that case, we return the universal (maximal) solution,
    unless there us no unique maximal solution.
    For example, in the polarity system, `*` (mixed) has lower-approximate left adjoints `{—, +, *}`, but this set of modalities
    does not have a join.
* related to type annotations (see `workOnTypes`):
  * for every mode `m`, a mode of types `ty m`
  * for every mode `m`, a **parametroid** modality `par m : ty m -> m`
  * a bar operation (parametroid conjugation), sending `µ : m -> n` to `bar µ : ty m -> ty n` defined by
    `bar µ = par n \ (µ º par m)` (TODO: check in degrees of relatedness paper).
    Since the function is defined, any more efficient implementation is easily quickcheckable.
* Sometimes, it is necessary to override the general behaviour. For example, a system for polarities will
  check the domain of a function type with negative modality and the codomain with a strictly positive Γ |—modality.

## Modal record fields and module entries

### Modal module entries

We understand fairly well how to use a definition annotated with a modality:
it can only be used in positions whose modality is greater.
However, if an annotated definition is in a module:

```agda
module (@ρ a : A) where
  postulate
    @µ b : B
```

then we need to assign `b` a type when viewed from outside the module.
Usually, this is done by just Π'ing up all the module parameters. However,
Π-types do not and should not take a modality annotation on their codomain.

#### Convert modal entries by left division (only if left adjoint)
One solution is to commute the modality with the module parameters by left dividing.
The above would thus be equivalent to

```agda
@µ b : (@(µ \ ρ) a : A) -> B a
```

However, the conversion from

```agda
(@ρ a : A) -> Box-µ B
```

to

```agda
Box-µ (   (@(µ \ ρ) a : A) -> B   )
```

is only definable internally if `µ` has an internal left adjoint
(i.e. if there is a modality `κ` such that `(κ º —) = (µ \ —)`).
In this case, the conversion is even an equivalence.

Even an approximate left adjoint `κ º µ ≤ id` is not good enough.

(The other conversion is always definable.)
So we should
**only allow modal annotations on definitions for modalities that have an internal left adjoint** (or otherwise the module should only be opened in telescopes, which we can then think of as a "pattern match").
In all other cases, users should wrap their definition in a modal datatype (which then has no projection, for good reasons!).

#### Directly interpret entries as top-level functions (not sound w.r.t. type-checking)
Note: perhaps we can be **slightly more permissive** and allow modal annotations for modalities which have a best approximation-from-below to their left adjoint. Then we do not convert module entry definitions (as this is not possible) but directly interpret them in the converted type.

To make sense of the following module:

```agda
module (@ρ a : A) where
  postulate
    @µ b : B
    @ν c : C
```

we then need to do

```agda
((@(µ \ ρ) a : A) -> B) -> ((@(ν \ µ) b : B) -> C) -> (@(ν \ ρ) a : A) -> C
```

i.e. we need `(ν \ µ) º (µ \ ρ) ≤ ν \ ρ`. Denote the approximate left adjoint by `µ*`. Then we have:

**Stop right there! This inequality is the wrong way!!!**

```
(ν \ µ) º (µ \ ρ) ≤ ν \ ρ
µ* º µ ≤ id
ν* º ν ≤ id
```

I haven't the faintest clue if this holds in general. I cannot prove it and cannot find a counterexample. Joris finds many counterexamples with a script in the list monad (awesome):

| μ    | ν    | ρ    | μ*   | ν*   |
| ---- | ---- | ---- | ---- | ---- |
| ++   | +    | +    | ++   | ++   |
| *    | —    | —    | *    | *    |
| *    | ++   | +    | —    | +    |
| b    | cont | cont | cont | cont |
| cont | b    | b    | cont | cont |
|      |      |      |      |      |

#### Type-check entries as top-level functions right away
This is of course possible and sound, but for the same reason that the above is unsound, the current approach will be counterintuitive, e.g. modal fields in the same module will not be accessible under the same conditions that modal variables are accessible (unless the concerned modality has a left adjoint). This is the current implementation of cohesion, even though flat does not have a left adjoint.
So in this case the user should get a warning if they annotate a field with a modality that does not have a left adjoint, with a recommendation to use a modal box instead.

Of course it is currently not possible to put a datatype declaration in a modal box. We should probably allow this.
The box should come before the parameters, which come before the colon, so we need syntax for a lock in a telescope.
I have no idea how to write the types of the constructors of a type that is caught in a box **for which we may have no eta, and perhaps not even a projection!**

So yes, let's just give users a warning to put datatypes in a box *without* any language support that makes such a thing possible.
Thanks to polarities, they can define their datatypes as the `Mu` of a strictly positive function and get the constructors for free.
This way, the box causes no headaches to the Agda implementors, only to the end user.

### Modal record fields

The simplest case of a record with a modal field, is a record with a single modal field, i.e.
the `Box-µ`-type. If there is a modality `θ` such that `θ º µ ≤ id`, then we can have

```agda
proj : @θ Box-µ A -> A
proj (box-µ a) = a
```

If we also have `id ≤ µ º θ` (meaning that `θ —| µ`), then we can state an η-rule for `proj`.
This η-rule can be proven propositionally by pattern-matching, is sound in most models, and
could be added as a definitional rule to Agda.

In short, I would propose to
**only allow modal annotations on fields only for modalities that have an internal left adjoint**. (If there are others, disable η and projections.)

#### η-rule

You cannot state the η-rule if you don't have a left adjoint, but only an approximate left adjoint `µ* º µ ≤ id`.

```
id ≤ µ º µ* (we don't know that)
-----------------------------------
a : Box-µ A, lock µ, lock µ* |– a : Box-µ A
-----------------------------------
a : Box-µ A, lock µ |— proj-µ-µ* a : A
-----------------------------------
a : Box-µ A |– box-µ (proj-µ-µ* a) : Box-µ A
-----------------------------------
a : Box-µ A |– box-µ (proj-µ-µ* a) = a : Box-µ A
```

So before `t : Box-µ A` can be η-expanded, we need to check that its η-expansion is well-typed. An exception is when `A` is judgementally a singleton; then we have to η-expand always.

Another issue is that η-expansion can be considered using any approximate left adjoint `μ*`. We could arbitrarily pick one (weird), take the least modality (doesn't fire often) or have η-expansion for each of the modalities, but then we have to relate the different projections. We could implement them via the eliminator, but then we have to make the eliminator depend irrelevantly on the modality.

### Left adjoints and approximate left adjoints

#### Relevance

##### Current

Shape-irrelevance and irrelevance have no left adjoint.

##### ParamDTT

The quotienting modalities (parametric, shape-irrelevance, irrelevance, parametric shape-irrelevance) have no left adjoint.

##### RelDTT

The quotienting modalities have no left adjoint.

##### Model of RelDTT

The crips modalities have no left adjoint, but you can use the left adjoint to their uncrispification.

#### Cohesion

Squash has no left adjoint.

Flat has no left adjoint, but continuity is a good approximation (you can continuously project from a flat box, but you can't state η).

#### Erasure

##### Erasure (current)

Erasure has no left adjoint.

##### Erasure (bimode)

We can get to a chain of adjoint modalities:

```
forgetCompileTime —| keepAtRuntime —| forgetRuntime —| trivialRuntime
```

and of course these compose, but the composites at `logicalMode` are always the identity modality. Now `forgetCompileTime` does not have a left adjoint.

By composing adjoints, we get a chain of adjoint (co)monads

```
runtimeAtCompileTime —| compileTimeAtRuntime —| erase
```

and the leftmost does not have a left adjoint.

#### Polarity

##### Without strict positivity

If we just have iso, pos, neg, mixed, then

```
iso:   no left adjoint
pos:   +  —|  +
neg:   —  —|  —
mixed: [+ | —] º * ≤ id
```

##### With strict positivity

```
iso:   no left adjoint
spos:  ++ —|  ++
pos:   ++ º + ≤ ++
neg:   —  º — ≤ ++
mixed: [+ | —] º * ≤ id
```

So we cannot use iso, pos, neg or mixed as annotations on fields and definitions.

## `workOnTypes` / The parametroid modality
### Intro
* In ParamDTT, type annotations on terms are checked under the parametric modality.
* In RelDTT, type annotations on terms at depth (mode) `d` are checked under the parametric modality `par : d+1 -> d`.
* In the current erasure system, type annotations on terms are checked under the erasure modality.
* In the proposed erasure system, type annotations on terms
  - at mode `programMode` should be checked under the modality `trivialRuntime : logicalMode -> programMode`,
  - at mode `logicalMode` should be checked under the identity modality
* In the cohesion system, type annotations are checked under the identity modality.

The common pattern here is that for every mode `m`, there is a mode `ty m` where the universe of `m`-types lives,
and a modality `par m : ty m -> m` for transporting types to the mode of their programs, where they can be used to annotate
these programs. We shall call `par m` the **parametroid** modality and `ty m` the mode of types.

### Presheaf semantics and Hofmann-Streicher universe
Any presheaf category is a CwF (category with families, model of dependent type theory) equipped with a model
of the universe, called the Hofmann-Streicher universe. Let us denote it by SetHS. It admits the following rule:
```
Γ |– A : SetHS
---------------
Γ |— ElHS A type
```
Of course we would usually omit `ElHS`.

In a sytem where universes are modelled as Hofmann-Streicher universes, the parametroid modality is just the identity.

However, when building a model, we can choose to model Agda's universe not as the Hofmann-Streicher universe, but as a
different universe, which we will denote just `Set`, from which there is a modal function
```
&m el : (@(par m) &(ty m) A : Set) -> SetHS
```
Then we get
```
par m \ Γ |— A : Set
------------------------
Γ |— el A : SetHS
------------------------
Γ |— ElHS (el A) type
```
which explains that e.g. a lambda-term for the non-modal function type, which would normally take a non-modal domain
annotation of type `SetHS`, can actually take a parametric domain annotation of type `Set`.

### Understanding parametroid modality via Hofmann-Streicher universe

#### Non-modal Π-type
With a universe à la Russell, such as `SetHS`, we generally have type constructors for the universe, type constructors
for the judgement, and equations relating both, such as
```
ElHS (πHS A (x.B)) = Π (ElHS A) (x.ElHS B)
```
Similarly, we would like to have type constructors at `Set` with equations such as
```
el (π A (x.B)) = πHS (el A) (x.el B)
```
Since these are really the equations that define `el`, we would like the RHS to be well-typed whenever the LHS is.
(The converse is not as much a requirement.)

Now the question is: how do we type-check this?

On the RHS, `A` is a parametroid subterm, so checked in `par m \ Γ`.
`B` is a parametroid subterm, and `x` is bound outside of `el`, so
`B` is checked in `par m \ (Γ , x : ElHS (el A))`.

This has to be consistent with what we find on the left. If we enter `el` on the left, we are
in `par m \ Γ`, so `A` is type-checked in the correct context. In `B`, we have to bind `x` with modality `par m \ id`.

#### Modal Π-type
Consider
```
el (π-µ A (x.B)) = πHS-µ (el A) (x.el B)
```
where `µ : m -> n`. The derivation tree is:
```
&(ty m) (µ º par) \ Γ |— A : Set
================================= rewrite context
&(ty m) par \ (µ \ Γ) |— A : Set                       &(ty n)  (par \ Γ), @(par \ µ) x : ElHS (el A) |— B : Set
---------------------------------                      -----------------------------------------------
&m      µ \ Γ |– el A : SetHS                          &n       Γ, @µ x : ElHS (el A) |– el B : SetHS
-----------------------------------------------------------------------------------------
&n      Γ |– πHS-µ (el A) (x.el B) : SetHS
```
On the left, we will check the domain under modality `bar µ : ty m -> ty n` and decide later how to compute `bar µ`.
In `B`, we clearly have to bind `x` with modality `par \ µ : m -> ty n`
The derivation tree is
```
&(ty m) (par º bar µ) \ Γ |— A : Set
==================================== rewrite context
&(ty m) bar µ \ (par \ Γ) |— A : Set                  &(ty n)  (par \ Γ), @(par \ µ) x : ElHS (el A) |— B : Set
---------------------------------------------------------------------------------------------------------------
&(ty n) par \ Γ |— π-µ A (x.B) : Set
--------------------------------------
&n      Γ |— el (π-µ A (x.B)) : SetHS
```
We want the RHS to be defined when the LHS is, i.e. if
```
&(ty m) (par º bar µ) \ Γ |— A : Set
```
is derivable then so should
```
&(ty m) (µ º par) \ Γ |— A : Set
```
so there should be a substitution
```
(µ º par) \ Γ   ->   (par º bar µ) \ Γ
```
i.e. (since left division is contravariant)
```
par º bar µ ≤ µ º par
```
In general, the *other* inequality holds. Fortunately, in RelDTT, this is an equality.
**Do we have a problem here when generalizing to arbitrary systems?**
Well I don't know, I guess `bar µ` can be anything solving the above inequality?
In the paper, we find however that the other inequality must also hold, so I guess we need to solve `bar µ` such that
`par º bar µ = µ º par`
i.e. we need a functor `ty : ModeTheory -> ModeTheory` and a natural transformation `par : ty -> id`.
