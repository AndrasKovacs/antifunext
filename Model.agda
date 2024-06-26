{-# OPTIONS --without-K --safe #-}

open import Agda.Primitive
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  renaming (subst to tr; sym to infix 5 _⁻¹; trans to infixr 4 _◼_; cong to ap)
  hiding ([_])

module Model where

--------------------------------------------------------------------------------

variable
  i j k l : Level

record Lift {i} j (A : Set i) : Set (i ⊔ j) where
  constructor ↑
  field
    ↓ : A
open Lift

-- CwF
--------------------------------------------------------------------------------

record Con i : Set (lsuc i) where
  field
    S : Set i
    P : S → Set i
open Con

record Sub (Γ : Con i)(Δ : Con j) : Set (i ⊔ j) where
  field
    S : Γ .S → Δ .S
    P : ∀ γ → Γ .P γ → Δ .P (S γ)
open Sub

record Ty {i} (Γ : Con i) j : Set (i ⊔ lsuc j) where
  field
    S : Γ .S → Set j
    P : ∀ γ → Γ .P γ → S γ → Set j
    E : ∀ γ → S γ
open Ty

record Tm {i}{j} (Γ : Con i) (A : Ty Γ j) : Set (i ⊔ j) where
  constructor tm
  field
    S : ∀ γ → A .S γ
    P : ∀ γ → (γᴾ : Γ .P γ) → A .P γ γᴾ (S γ)
open Tm

variable
  Γ Δ Ξ ξ : Con _
  A B C D : Ty _ _
  σ δ ν   : Sub _ _
  t u v   : Tm _ _

∙ : Con lzero
S ∙   = ⊤
P ∙ _ = ⊤

ε : Sub Γ ∙
S ε _   = tt
P ε _ _ = tt

εη : {σ : Sub Γ ∙} → σ ≡ ε
εη = refl

infixl 3 _▶_
_▶_ : (Γ : Con i) → Ty Γ j → Con (i ⊔ j)
S (Γ ▶ A)         = Σ (Γ .S) (A .S)
P (Γ ▶ A) (γ , α) = Σ (Γ .P γ) λ γᴾ → A .P γ γᴾ α

id : Sub Γ Γ
S id γ    = γ
P id γ γᴾ = γᴾ

infixr 5 _∘_
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
_[_]T : Ty Γ i → Sub {j}{k} Δ Γ → Ty Δ i
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

p : (A : Ty {i} Γ j) → Sub (Γ ▶ A) Γ
S (p A)   (γ  , _) = γ
P (p A) _ (γᴾ , _) = γᴾ

q : ∀ {Γ : Con i}(A : Ty Γ j) → Tm (Γ ▶ A) (A [ p A ]T)
S (q A)   (_ , α)  = α
P (q A) _ (_ , αᴾ) = αᴾ

_,ₛ_ : (σ : Sub Γ Δ) → Tm {i}{j} Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
S (σ ,ₛ t) γ    = σ .S γ    , t .S γ
P (σ ,ₛ t) γ γᴾ = σ .P γ γᴾ , t .P γ γᴾ

pβ : ∀ {Γ Δ A}{σ : Sub {i}{j} Γ Δ}{t : Tm {i}{k} Γ (A [ σ ]T)} → (p A ∘ (_,ₛ_ {A = A} σ t)) ≡ σ
pβ = refl

qβ : ∀ {Γ Δ A}{σ : Sub {i}{j} Γ Δ}{t : Tm {i}{k} Γ (A [ σ ]T)} → (q A [ _,ₛ_ {A = A} σ t ]) ≡ t
qβ = refl

,ₛη : (p A ,ₛ q A) ≡ id
,ₛη = refl

,ₛ∘ : ∀ {A}{σ : Sub Γ Δ}{t : Tm {i}{j} Γ (A [ σ ]T)}{δ : Sub Ξ Γ}
      → (_,ₛ_ {A = A} σ t) ∘ δ ≡ (_,ₛ_ {A = A} (σ ∘ δ) (t [ δ ]))
,ₛ∘ = refl

-- redefining (σ ∘ p ,ₛ q), just because Agda inference kinda fails
-- if I write it out internally
lift : (σ : Sub {i}{j} Γ Δ)(A : Ty Δ k) → Sub (Γ ▶ A [ σ ]T) (Δ ▶ A)
S (lift σ A) (γ , α)           = S σ γ , α
P (lift σ A) (γ , α) (γᴾ , αᴾ) = (P σ γ γᴾ) , αᴾ

-- Universes
--------------------------------------------------------------------------------

U : ∀ i → Ty Γ (lsuc i)
S (U i) γ            = Σ (Set i) λ A → A
P (U i) γ γᴾ (A , _) = A → Set i
E (U i) γ            = Lift _ ⊤ , ↑ tt

U[] : U i [ σ ]T ≡ U i
U[] = refl

El : Tm Γ (U i) → Ty Γ i
S (El a) γ      = a .S γ .₁
P (El a) γ γᴾ x = a .P _ γᴾ x
E (El a) γ      = a .S γ .₂

El[] : ∀ {σ : Sub {i}{j} Γ Δ}{t : Tm Δ (U k)} → El t [ σ ]T ≡ El (t [ σ ])
El[] = refl

code : Ty Γ i → Tm Γ (U i)
S (code A) γ      = A .S γ , A .E γ
P (code A) γ γᴾ a = A .P _ γᴾ a

Elcode : El (code A) ≡ A
Elcode = refl

codeEl : code (El t) ≡ t
codeEl = refl


-- Pi
--------------------------------------------------------------------------------

Pi : ∀ {i j k Γ}(A : Ty {i} Γ j) → Ty (Γ ▶ A) k → Ty Γ (j ⊔ k)
S (Pi A B) γ      = (x : A .S γ) → B .S (γ , x)
P (Pi A B) γ γᴾ f = (x : A .S γ)(xᴾ : A .P γ γᴾ x) → B .P (γ , x) (γᴾ , xᴾ) (f x)
E (Pi A B) γ x    = B .E (γ , x)

Pi[] : Pi {i}{j}{k}{Γ} A B [ σ ]T ≡ Pi {i}{j}{k}{Δ} (A [ σ ]T) (B [ _,ₛ_ {A = A} (σ ∘ p (A [ σ ]T) )  (q (A [ σ ]T)) ]T)
Pi[] = refl

Lam : Tm (Γ ▶ A) B → Tm Γ (Pi {i}{j = j}{k = k} A B)
S (Lam t) γ x       = t .S (γ , x)
P (Lam t) γ γᴾ x xᴾ = t .P (γ , x) (γᴾ , xᴾ)

Lam[] : ∀ {i' i j k Γ Δ}{σ : Sub {i'}{i} Δ Γ}{A : Ty {i} Γ j}{B : Ty (Γ ▶ A) k}{t : Tm (Γ ▶ A) B}
        → Lam {A = A} t [ σ ] ≡ Lam {A = A [ σ ]T} (t [ lift σ A ])
Lam[] = refl

App : ∀ {i j k Γ A B} → Tm Γ (Pi {i}{j = j}{k = k} A B) → Tm (Γ ▶ A) B
S (App t) (γ , x)           = t .S γ x
P (App t) (γ , x) (γᴾ , xᴾ) = t .P γ γᴾ x xᴾ

Piβ : App {i}{j}{k}{Γ}{A} (Lam t) ≡ t
Piβ = refl

Piη : Lam {i}{Γ}{j}{A}{k} (App t) ≡ t
Piη = refl

-- Sigma
--------------------------------------------------------------------------------

Sg : ∀ {i j k Γ}(A : Ty {i} Γ j) → Ty (Γ ▶ A) k → Ty Γ (j ⊔ k)
S (Sg A B) γ = Σ (A . S γ) λ α → B .S (γ , α)
P (Sg A B) γ γᴾ (α , β) = Σ (A .P _ γᴾ α) λ αᴾ → B .P _ (γᴾ , αᴾ) β
E (Sg A B) γ = (A .E γ) , B .E (γ , (A .E γ))

Sg[] : ∀ {i' i j k Δ Γ A B}{σ : Sub {i'}{i} Δ Γ}
       → Sg {i}{j}{k}{Γ} A B [ σ ]T ≡ Sg {i'}{j}{k}{Δ} (A [ σ ]T) (B [ lift σ A ]T)
Sg[] = refl

Pair : ∀ {i j k Γ}{A : Ty {i} Γ j}{B : Ty (Γ ▶ A) k} → (t : Tm Γ A) → Tm Γ (B [ id ,ₛ t ]T) → Tm Γ (Sg A B)
S (Pair t u) γ    = (t .S γ) , u .S γ
P (Pair t u) γ γᴾ = (t .P γ γᴾ) , (u .P γ γᴾ)

Pair[] : ∀ {σ : Sub {l}{i} Δ Γ} → Pair {i}{j}{k}{Γ}{A}{B} t u [ σ ] ≡
                                  Pair {l}{j}{k}{Δ}{A [ σ ]T} {B [ lift σ A ]T} (t [ σ ]) (u [ σ ])
Pair[] = refl

Fst : Tm Γ (Sg A B) → Tm Γ A
S (Fst t) γ = ₁ (S t γ)
P (Fst t) γ Γᴾ = ₁ (P t γ Γᴾ)

Snd : ∀ {i j k Γ}{A : Ty Γ j}{B : Ty (Γ ▶ A) k}(t : Tm {i} Γ (Sg A B)) → Tm Γ (B [ id ,ₛ Fst {B = B} t ]T)
S (Snd t) γ = ₂ (S t γ)
P (Snd t) γ Γᴾ = ₂ (P t γ Γᴾ)

Fstβ : ∀ {i j k Γ}{A : Ty {i} Γ j}{B : Ty (Γ ▶ A) k}{t : Tm Γ A}{u : Tm Γ (B [ id ,ₛ t ]T)}
       → Fst {B = B} (Pair {B = B} t u) ≡ t
Fstβ = refl

Sndβ : ∀ {i j k Γ}{A : Ty {i} Γ j}{B : Ty (Γ ▶ A) k}{t : Tm Γ A}{u : Tm Γ (B [ id ,ₛ t ]T)}
       → Snd {B = B} (Pair {B = B} t u) ≡ u
Sndβ = refl

-- Nat
--------------------------------------------------------------------------------

data ℕ* : Set where
  zero : ℕ*
  suc  : ℕ* → ℕ*
  err  : ℕ*

ℕ*-elim : (B : ℕ* → Set i) → B zero → B err → (∀ {n} → B n → B (suc n)) → ∀ n → B n
ℕ*-elim B z e s zero    = z
ℕ*-elim B z e s (suc n) = s (ℕ*-elim B z e s n)
ℕ*-elim B z e s err     = e

data ℕᴾ :  ℕ* → Set where
  zero : ℕᴾ zero
  suc  : ∀ {n} → ℕᴾ n → ℕᴾ (suc n)

ℕᴾ-elim : (B : ∀ {n} → ℕᴾ n → Set i) → B zero → (∀ {n}{nᴾ} → B {n} nᴾ → B (suc nᴾ)) → ∀ {n} nᴾ → B {n} nᴾ
ℕᴾ-elim B z s zero    = z
ℕᴾ-elim B z s (suc n) = s (ℕᴾ-elim B z s n)

Nat : Ty {i} Γ lzero
S Nat _   = ℕ*
P Nat _ _ = ℕᴾ
E Nat _   = err

Nat[] : Nat [ σ ]T ≡ Nat
Nat[] = refl

Zero : Tm Γ Nat
S Zero γ    = zero
P Zero _ γᴾ = zero

Zero[] : Zero [ σ ] ≡ Zero
Zero[] = refl

Suc : Tm Γ Nat → Tm Γ Nat
S (Suc t) γ    = suc (t .S γ)
P (Suc t) _ γᴾ = suc (t .P _ γᴾ)

Suc[] : (Suc t) [ σ ] ≡ Suc (t [ σ ])
Suc[] = refl

NatElim : ∀{i j}{Γ : Con i}(B : Ty (Γ ▶ Nat) j)
          → Tm Γ (B [ id ,ₛ Zero ]T)
          → Tm (Γ ▶ Nat ▶ B) (B [ (p Nat ∘ p B) ,ₛ (Suc (q Nat [ p B ])) ]T)
          → (n : Tm Γ Nat) → Tm Γ (B [ id ,ₛ n ]T)
S (NatElim {i} {j} {Γ} B pz ps n) γ =
  ℕ*-elim (λ nSγ → B .S (γ , nSγ)) (pz .S γ) (B .E (γ , err))
          (λ n → ps .S ((γ , _) , n))
          (n .S γ)
P (NatElim {i} {j} {Γ} B bz bs n) γ γᴾ =
    ℕᴾ-elim (λ {nSγ} nPγγᴾ → B .P (γ , nSγ) (γᴾ , nPγγᴾ)
      (ℕ*-elim (λ nSγ → B .S (γ , nSγ)) (bz .S γ) (B .E (γ , err))
       (λ n₁ → bs .S ((γ , _) , n₁)) nSγ))
      (bz .P _ γᴾ)
      (λ {_}{nᴾ} hyp → bs .P _ ((γᴾ , nᴾ) , hyp))
      (n .P _ γᴾ)

NatElim[] : ∀ {i' i j Δ Γ}{σ : Sub {i'}{i} Δ Γ}{B z s n}
            → NatElim {i}{j}{Γ} B z s n [ σ ]
            ≡ NatElim (B [ (σ ∘ p Nat) ,ₛ q Nat ]T) (z [ σ ]) (s [ lift (lift σ Nat) B ]) (n [ σ ])
NatElim[] = refl

NatElimZero : ∀{i j Γ B z s} → NatElim {i}{j}{Γ} B z s Zero ≡ z
NatElimZero = refl

NatElimSuc : ∀{i j Γ B z s n}
             → NatElim {i}{j}{Γ} B z s (Suc n)
             ≡ s [ _,ₛ_ {A = B} (id ,ₛ n)  (NatElim B z s n) ]
NatElimSuc = refl


-- Id
--------------------------------------------------------------------------------

data Id* {i}{A : Set i} (a : A) : A → Set i where
  refl : Id* a a
  err  : ∀ b → Id* a b

data Idᴾ {i}{A : Set i}(Aᴾ : A → Set i) : ∀ {x y : A}(xᴾ : Aᴾ x)(yᴾ : Aᴾ y) → Id* x y → Set i where
  refl : ∀ {x}(xᴾ : Aᴾ x) → Idᴾ Aᴾ xᴾ xᴾ refl

J* : ∀ {A : Set i}{a : A}(B : ∀ x → Id* {A = A} a x → Set j)
                  → B a refl → (∀ x → B x (err x)) → ∀ {x}(p : Id* a x) → B x p
J* B r e refl    = r
J* B r e (err x) = e x

J*ᴾ : ∀ {A : Set i}{Aᴾ : A → Set i}{a : A}{aᴾ : Aᴾ a}(B : ∀ x xᴾ (e : Id* {A = A} a x) → Idᴾ Aᴾ aᴾ xᴾ e → Set j)
                  → B a aᴾ refl (refl _) → ∀ {x xᴾ}(e : Id* a x)(eᴾ : Idᴾ Aᴾ aᴾ xᴾ e) → B x xᴾ e eᴾ
J*ᴾ B br .refl (refl _) = br

Id : (A : Ty {i} Γ j) → Tm Γ A → Tm Γ A → Ty Γ j
S (Id A t u) γ    = Id* {A = A .S γ} (t .S γ) (u .S γ)
P (Id A t u) γ γᴾ = Idᴾ {A = A .S γ}(A .P γ γᴾ) (t .P γ γᴾ) (u .P γ γᴾ)
E (Id A t u) γ    = err (u .S γ)

Id[] : Id A t u [ σ ]T ≡ Id (A [ σ ]T) (t [ σ ]) (u [ σ ])
Id[] = refl

Refl : ∀ (t : Tm {i}{j} Γ  A) → Tm Γ (Id A t t)
S (Refl t) γ    = refl
P (Refl t) γ γᴾ = refl _

Refl[] : Refl t [ σ ] ≡ Refl (t [ σ ])
Refl[] = refl

-- substitutions defined externally, again to avoid implicit arg inference issues
-- ((id ,ₛ a) ,ₛ Refl a)
rsub : ∀ Γ A (a : Tm {i}{j} Γ A) → Sub Γ (Γ ▶ A ▶ Id (A [ p A ]T) (a [ p A ]) (q A))
S (rsub Γ A a) γ    = (γ , a .S γ) , refl
P (rsub Γ A a) γ γᴾ = (γᴾ , a .P γ γᴾ) , refl _

-- ((id ,ₛ a') ,ₛ e)
esub : ∀ Γ A (a a' : Tm {i}{j} Γ A)(e : Tm Γ (Id A a a')) → Sub Γ (Γ ▶ A ▶ Id (A [ p A ]T) (a [ p A ]) (q A))
S (esub Γ A a a' e) γ    = (γ  , a' .S γ)    , e .S γ
P (esub Γ A a a' e) γ γᴾ = (γᴾ , a' .P γ γᴾ) , e .P γ γᴾ

J' : ∀ {i j k Γ}{A : Ty {i} Γ j}{a : Tm Γ A}
     → (B : Ty (Γ ▶ A ▶ Id (A [ p A ]T) (a [ p A ]) (q A)) k)
     → Tm Γ (B [ rsub Γ A a ]T)
     → (a' : Tm Γ A)
     → (e  : Tm Γ (Id A a a'))
     → Tm Γ (B [ esub Γ A a a' e ]T)
S (J' {i} {Γ} {j} {k} {A} {a} B br a' e) γ =
  J* (λ a'Sγ eSγ → B .S ((γ , a'Sγ) , eSγ)) (br .S γ) (λ x → B .E ((γ , x) , err x)) (e .S γ)
P (J' {i} {Γ} {j} {k} {A} {a} B br a' e) γ γᴾ =
  J*ᴾ (λ a'Sγ a'Pγγᴾ eSγ ePγγᴾ → B .P ((γ , a'Sγ) , eSγ) ((γᴾ , a'Pγγᴾ) , ePγγᴾ)
         (J* (λ a'Sγ eSγ → B .S ((γ , a'Sγ) , eSγ)) (br .S γ)
          (λ x → B .E ((γ , x) , err x)) (eSγ)))
       (br .P γ γᴾ)
       (S e γ)
       (e .P γ γᴾ)

J'β : ∀ {i j k Γ A a B br} → J' {i}{j}{k}{Γ}{A}{a} B br a (Refl a) ≡ br
J'β = refl

-- helper for lifting σ, again written separately because of inference issues
liftσ : ∀ {i' i j Γ Δ}(σ : Sub {i'}{i} Δ Γ){A : Ty {i} Γ j}(a : Tm Γ A)
      → Sub
        (Δ ▶ A [ σ ]T ▶ Id ((A [ σ ]T) [ p (A [ σ ]T) ]T) ((a [ σ ]) [ p (A [ σ ]T) ]) (q (A [ σ ]T)))
        (Γ ▶ A ▶ Id (A [ p A ]T) (a [ p A ]) (q A))
S (liftσ {i'} {i} {j} {Γ} {Δ} σ {A} a) ((δ , α) , e) = (σ .S δ , α) , e
P (liftσ {i'} {i} {j} {Γ} {Δ} σ {A} a) ((δ , α) , e) ((δᴾ , αᴾ) , eᴾ) = (P σ δ δᴾ , αᴾ) , eᴾ

J'[] : ∀ {i' i j k}{Δ Γ}{σ : Sub {i'}{i} Δ Γ}{A a B br a' e}
     → J' {i}{j}{k}{Γ}{A}{a} B br a' e [ σ ]
     ≡ J' {i'}{j}{k}{Δ}{A [ σ ]T}{a [ σ ]} (B [ liftσ σ a ]T) (br [ σ ]) (a' [ σ ]) (e [ σ ])
J'[] = refl


--------------------------------------------------------------------------------

module NoFunExt where
  FunExtTy : ∀ {i j k} → Set (lsuc i ⊔ lsuc j ⊔ lsuc k)
  FunExtTy {i}{j}{k} =
           ∀ {Γ A B}(f g : Tm Γ (Pi {i}{j}{k} A B))
           → Tm (Γ ▶ A) (Id B (App {A = A} f) (App {A = A} g))
           → Tm Γ (Id (Pi A B) f g)

  One : Ty Γ lzero
  S One _     = Bool
  P One _ _ x = x ≡ true
  E One _     = false

  f : Tm Γ (Pi One One)
  S f _ x = x
  P f _ _ _ refl = refl

  g : Tm Γ (Pi One One)
  S g _ _ = true
  P g _ _ _ _ = refl

  e : Tm (∙ ▶ One) (Id One (App {A = One} f) (App {A = One} g))
  S e   (_ , true)  = refl
  S e   (_ , false) = err true
  P e _ (_ , refl ) = refl refl

  lem : ∀ {i A Aᴾ x y xᴾ yᴾ e} → Idᴾ {i}{A} Aᴾ {x}{y} xᴾ yᴾ e → x ≡ y
  lem (refl _) = refl

  ¬FunExt : (∀ {i j k} → FunExtTy {i}{j}{k}) → ⊥
  ¬FunExt fext with ap (λ f → f false) (lem (fext {A = One} f g e . P _ _))
  ... | ()
