{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Lib

module Model where

--------------------------------------------------------------------------------

record Lift (A : Set) : Set₁ where
  constructor ↑
  field
    ↓ : A
open Lift public

-- CwF
--------------------------------------------------------------------------------

record Con : Set₂ where
  field
    S : Set₁
    P : S → Set₁
open Con public

record Sub (Γ Δ : Con) : Set₁ where
  field
    S : Γ .S → Δ .S
    P : ∀ γ → Γ .P γ → Δ .P (S γ)
open Sub public

record Ty (Γ : Con) : Set₂ where
  field
    S : Γ .S → Set₁
    P : ∀ γ → Γ .P γ → S γ → Set₁
    E : ∀ γ → S γ
open Ty public

record Tm (Γ : Con) (A : Ty Γ) : Set₁ where
  field
    S : ∀ γ → A .S γ
    P : ∀ γ → (γᴾ : Γ .P γ) → A .P γ γᴾ (S γ)
open Tm public

variable
  Γ Δ Ξ ξ : Con
  A B C D : Ty _
  σ δ ν   : Sub _ _
  t u v   : Tm _ _

∙ : Con
S ∙   = Lift ⊤
P ∙ _ = Lift ⊤

ε : Sub Γ ∙
S ε _   = ↑ tt
P ε _ _ = ↑ tt

εη : {σ : Sub Γ ∙} → σ ≡ ε
εη = refl

infixl 3 _▶_
_▶_ : (Γ : Con) → Ty Γ → Con
S (Γ ▶ A)         = Σ (Γ .S) (A .S)
P (Γ ▶ A) (γ , α) = Σ (Γ .P γ) λ γᴾ → A .P γ γᴾ α

id : Sub Γ Γ
S id γ    = γ
P id γ γᴾ = γᴾ

_∘_ : Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
S (σ ∘ δ) γ    = S σ (S δ γ)
P (σ ∘ δ) γ γᴾ = P σ (S δ γ) (P δ γ γᴾ)

idl : id ∘ σ ≡ σ
idl = refl

idr : σ ∘ id ≡ σ
idr = refl

ass : σ ∘ (δ ∘ ν) ≡ (σ ∘ δ) ∘ ν
ass = refl

infix 5 _[_]T
_[_]T : Ty Γ → Sub Δ Γ → Ty Δ
S (A [ σ ]T) γ      = A .S (σ .S γ)
P (A [ σ ]T) γ γᴾ α = A .P (σ .S γ) (σ .P γ γᴾ) α
E (A [ σ ]T) γ      = A .E (σ .S γ)

[id]T : A [ id ]T ≡ A
[id]T = refl

[∘]T : A [ σ ]T [ δ ]T ≡ (A [ σ ]T) [ δ ]T
[∘]T = refl

infix 5 _[_]
_[_] : Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (A [ σ ]T)
S (t [ σ ]) γ    = t .S (σ .S γ)
P (t [ σ ]) γ γᴾ = t .P (σ .S γ) (σ .P γ γᴾ)

p : ∀ A → Sub (Γ ▶ A) Γ
S (p A)   (γ  , _) = γ
P (p A) _ (γᴾ , _) = γᴾ

q : ∀ A → Tm (Γ ▶ A) (A [ p A ]T)
S (q A)   (_ , α)  = α
P (q A) _ (_ , αᴾ) = αᴾ

_,ₛ_ : (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
S (σ ,ₛ t) γ    = σ .S γ    , t .S γ
P (σ ,ₛ t) γ γᴾ = σ .P γ γᴾ , t .P γ γᴾ

pβ : ∀ {Γ Δ A}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)} → (p A ∘ (_,ₛ_ {A = A} σ t)) ≡ σ
pβ = refl

qβ : ∀ {Γ Δ A}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)} → (q A [ _,ₛ_ {A = A} σ t ]) ≡ t
qβ = refl

,ₛη : (p A ,ₛ q A) ≡ id
,ₛη = refl

,ₛ∘ : ∀ {A}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}{δ : Sub Ξ Γ}
      → (_,ₛ_ {A = A} σ t) ∘ δ ≡ (_,ₛ_ {A = A} (σ ∘ δ) (t [ δ ]))
,ₛ∘ = refl

--------------------------------------------------------------------------------

data OneErr : Set where
  one err : OneErr

U : Ty Γ
S (U {Γ}) γ            = Σ Set λ A → A
P (U {Γ}) γ γᴾ (A , a) = A → Set
E (U {Γ}) γ            = OneErr , err

El : Tm Γ U → Ty Γ
S (El a) γ          = Lift (a .S γ .₁)
P (El a) γ γᴾ (↑ x) = Lift (a .P _ γᴾ x)
E (El a) γ          = ↑ (a .S γ .₂)
