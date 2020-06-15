# Notes on Conor McBride unpublished *Type-Preserving Renaming and Substitution*

These notes are written in order to understand the paper and the
programming technique presented in it. There is nothing original
in these notes.

In this paper, Conor McBride proposes a programming technique that
allows to define in a generic manner renaming and substitution on a
lambda calculus defined ad an inductive type family (Altenkirch and
Reus 1999).

The code in the original paper is written in Epigram. I translate it in
Agda. I mostly keep the original names and notations.


```agda
module TPRS where
```

Firstly, let's define the priorities for the mixfix operators we are
going to use.

```agda
infixr 10 _▷_
infixl  7 _,_
infix   5 _▶_
infix   5 _∋_
```

Then we define an inductive data type for the types of our object
language. The simply types lambda calculus has only two types, a
ground type and the function type, the latter being defined
inductively.

```agda
data Ty : Set where
  ∙ : Ty
  _▷_ : Ty -> Ty -> Ty
```

As the variables in our object language are either bound by a binder
(a lambda abstraction) or in a context, we need to define a data type
of context which is just a list of types as we use De Bruijn
indexes. In a similar way than the traditional presentation of
context, we use a `snoc` list.

```agda
data Ctxt : Set where
  ε : Ctxt
  _,_ : Ctxt -> Ty -> Ctxt
```

In order to code De Bruijn indexes, we use membership proof that are
isomorphic to Peano natural numbers.


```agda
data _∋_ : Ctxt -> Ty -> Set where

  vz : ∀ {Γ T}
    ------------
    -> Γ , T ∋ T
    
  vs : ∀ {Γ T S}
    -> Γ ∋ T
    ------------
    -> Γ , S ∋ T
```

We now can define the syntax of our object language. A term depends on
the context in which it is valid and its type. This allows us to trust
the host language's typechecker (agda's typechecker) to maintain the terms
well-scoped and well-typed.

```agda
data _▶_ : Ctxt -> Ty -> Set where

  var : forall {Γ T}
    -> Γ ∋ T
    --------
    -> Γ ▶ T
    
  lda : forall {Γ T S}
    -> Γ , S ▶ T
    ------------
    -> Γ ▶ T ▷ S
    
  app : forall {Γ T S}
    -> Γ ▶ T ▷ S
    -> Γ ▶ T
    --------
    -> Γ ▶ S
```

Now that our object language is defined, we can tackle the main object
of the paper: the generic definition of renaming and substitution of
our De Bruijn terms.

The idea is to pack all the functions we'll need for renaming and
substitution in a `Kit` so that we will be able to define a traversal
operation that is parametrised by a `Kit`.

A `Kit` is a type family indexed by a type constructor (_◆_) that
takes a context and a type. In the framework already defined, this is
the type of the membership proof (_∋_), *ie* a variable identifier,
and of a term (_▶_).

In order to understand the `Kit` idea, it is important to note that
both renaming and substitution operate a traversal of a term replacing
variables by something. Renaming replaces variables by variables and
substitution replaces variables by terms. So the general idea is that
_◆_ can be either a variable identifier or a term.

The `vr` field contains a function that turns a variable identifier
into the corresponding *stuff*, either a variable identifier or a
term. It is used in the `lift` function (called whenever we cross a
binder in our traversal) in the case we cross the variable binded to
the closest binder (the latest abstraction). In the case of renaming,
`vr` is defined as the identity function as we don't want to rename
the new bound variable. In the case of substitution, is is defined
as `var` as we don't want to susbtitute the new bound variable.

The `tm` field contains a function that turns one of this *diamond
stuff* into a term. It is used in the traversal operation whenever we
cross a variable, its identifier first being turned into a diamond
stuff by a given map (τ).

In the case of renaming, `tm` is defined as the `var` term
constructor.  The diamond stuff being variable identifier, we want to
build a variable with a transformed variable identifier. We note that
`rename` is only used to defined `wk` of the Kit for the `subst`
function, the given map being `vs`, that is the equivalent of the
successor constructor for membership proof. In fact, renaming is
basically the operation of incrementing the De Bruijn indexes.

In the case of substitution, `tm` is defined as the identity function,
all the work is done by the second argument, the map that turns
variable identifiers into terms.

The `wk` field contains, as its name may suggest, a weakening
function, that is a function that add a new type to the context with
the guaranty of type preservation of the diamond stuff.

`wk` is only used in the second case of the `lift` function. That
makes sense because the `lift` function weakens, so to speak, a type
preserving map that turns a variable indentifier in a context Γ to a
diamond stuff in context Δ.

```agda
record Kit (_◆_ : Ctxt -> Ty -> Set) : Set where
  constructor kit
  field
    vr : ∀ {Γ T} -> Γ ∋ T -> Γ ◆ T
    tm : ∀ {Γ T} -> Γ ◆ T -> Γ ▶ T
    wk : ∀ {Γ T S} -> Γ ◆ T -> (Γ , S) ◆ T
```

The lift function is a general weakening function called whenever we
cross a binder in the traversal.

```agda
lift : ∀ {Γ Δ T S}{_◆_ : Ctxt -> Ty -> Set} -> Kit _◆_ -> (∀ {X} -> Γ ∋ X -> Δ ◆ X) -> Γ , S ∋ T -> (Δ , S) ◆ T
lift (kit vr tm wk) τ vz = vr vz
lift (kit vr tm wk) τ (vs x) = wk (τ x)
```

The traversal takes a Kit and a function that turns variable
identifiers into diamond stuff (and of course a term to traverse).  It
calls `tm` on the transformed variable identiers, lift the body of the
lambda abstraction before traversing them and traverse recursively the
two terms composing an application.

```agda
trav : ∀ {Γ Δ T}{_◆_ : Ctxt -> Ty -> Set} -> Kit (_◆_) -> (∀ {X} -> Γ ∋ X -> Δ ◆ X) -> Γ ▶ T -> Δ ▶ T
trav (kit vr tm wk) τ (var x) = tm (τ x)
trav K τ (lda t) = lda (trav K (lift K τ) t) 
trav K τ (app t t₁) = app (trav K τ t) (trav K τ t₁)
```

`rename` traverse a term incrementing every De Bruijn indexes that need to be.

```agda
rename : ∀ {Γ Δ T} -> (∀ {X} -> Γ ∋ X -> Δ ∋ X) -> Γ ▶ T -> Δ ▶ T
rename ρ t = trav (kit (λ x -> x) var vs) ρ t
```

`subst` traverse a term replacing variable accordingly to a substitution map (σ)

```agda
subst : ∀ {Γ Δ T} -> (∀ {X} -> Γ ∋ X -> Δ ▶ X) -> Γ ▶ T -> Δ ▶ T
subst σ t = trav (kit var (λ x → x) (rename vs)) σ t

```
