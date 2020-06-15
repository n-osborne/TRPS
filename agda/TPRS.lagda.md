# Notes on Conor McBride unpublished *Type-Preserving Renaming and Substitution*



```agda

module TPRS where


infixr 10 _▷_ 
infixl  7 _,_
infix   5 _▶_
infix   5 _∋_

data Ty : Set where
  ∙ : Ty
  _▷_ : Ty -> Ty -> Ty

data Ctxt : Set where
  ε : Ctxt
  _,_ : Ctxt -> Ty -> Ctxt

data _∋_ : Ctxt -> Ty -> Set where
  vz : ∀ {Γ T} -> Γ , T ∋ T
  vs : ∀ {Γ T S} -> Γ ∋ T -> Γ , S ∋ T

data _▶_ : Ctxt -> Ty -> Set where
  var : forall {Γ T} -> Γ ∋ T -> Γ ▶ T
  lda : forall {Γ T S} -> Γ , S ▶ T -> Γ ▶ T ▷ S
  app : forall {Γ T S} -> Γ ▶ T ▷ S -> Γ ▶ T -> Γ ▶ S

record Kit (_◆_ : Ctxt -> Ty -> Set) : Set where
  constructor kit
  field
    vr : ∀ {Γ T} -> Γ ∋ T -> Γ ◆ T
    tm : ∀ {Γ T} -> Γ ◆ T -> Γ ▶ T
    wk : ∀ {Γ T S} -> Γ ◆ T -> (Γ , S) ◆ T

lift : ∀ {Γ Δ T S}{_◆_ : Ctxt -> Ty -> Set} -> Kit _◆_ -> (∀ {X} -> Γ ∋ X -> Δ ◆ X) -> Γ , S ∋ T -> (Δ , S) ◆ T
lift (kit vr tm wk) τ vz = vr vz
lift (kit vr tm wk) τ (vs x) = wk (τ x)

trav : ∀ {Γ Δ T}{_◆_ : Ctxt -> Ty -> Set} -> Kit (_◆_) -> (∀ {X} -> Γ ∋ X -> Δ ◆ X) -> Γ ▶ T -> Δ ▶ T
trav (kit vr tm wk) τ (var x) = tm (τ x)
trav K τ (lda t) = lda (trav K (lift K τ) t) 
trav K τ (app t t₁) = app (trav K τ t) (trav K τ t₁)

rename : ∀ {Γ Δ T} -> (∀ {X} -> Γ ∋ X -> Δ ∋ X) -> Γ ▶ T -> Δ ▶ T
rename ρ t = trav (kit (λ x -> x) var vs) ρ t

subst : ∀ {Γ Δ T} -> (∀ {X} -> Γ ∋ X -> Δ ▶ X) -> Γ ▶ T -> Δ ▶ T
subst σ t = trav (kit var (λ x → x) (rename vs)) σ t

```
