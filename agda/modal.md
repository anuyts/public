# Proposal: Multimode Agda
J.w.w. Malin Altenmüller, Joris Ceulemans, Lucas Escot, Josselin Poiret

## Short list of things to be done

- Abstract mode theory interface, with several orthogonal instances
   - relevance
   - cohesion
   - quantity (unless viewed as substructural)
   - polarity
   - guarded
   - easy to add
- Interface
   - order
   - composition & left division
      - quickcheck unit & co-unit
   - NO addition
   - mode of types
   - parametric modality
   - parametric conjugation (overridable default implementation)
      - quickcheck
   - unit modality
   - default modality for functions
   - default modality for definitions
- Quantity
   - either a 2-mode system
   - or substructural
- Mode
   - Annotate judgement (i.e. TCM) with a mode instead of a modality
- Modal module & record fields
- Think about future support for explicit 2-cells
- Maximal annotation for functions
- Syntax
   - maybe be principled, eg `pol:++`, `coh:\b`, ...

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
                 +-----------------<---------------+     +-->--+
                /                                   \   /      |
             timeless              ⊥               timeful     | later
                \                                   /   \      |
                 +----------------->---------------+     +--<--+
                                forever
```
where `constantly º forever = id : timeless -> timeless`
and `always = forever º constantly : timeful -> timeful` is a comonad.

To obtain multiclock type theory, we could take the free (cartesian
category with same terminal object) over this category, but clocks
will be meta-things (e.g. natural numbers).
The tick-based approach to guarded type theory is better suited
to be extended with multiple clocks.

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

Even an approximate left adjoint `κ º µ ≤ id` is not good enough.

(The other conversion is always definable.)
So we should
**only allow modal annotations on definitions for modalities that have an internal left adjoint** (or otherwise the module should only be opened in telescopes, which we can then think of as a "pattern match").
In all other cases, users should wrap their definition in a modal datatype (which then has no projection, for good reasons!).

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

### Whatever
