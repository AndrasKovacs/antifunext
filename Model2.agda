{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Lib

module Model2 where

--------------------------------------------------------------------------------

variable
  i j k l : Level

record Lift {i} j (A : Set i) : Set (i ⊔ j) where
  constructor ↑
  field
    ↓ : A
open Lift public


-- CwF
--------------------------------------------------------------------------------

record Con i : Set (lsuc i) where
  field
    S : Set i
    P : S → Set i
open Con public

record Sub (Γ : Con i)(Δ : Con j) : Set (i ⊔ j) where
  field
    S : Γ .S → Δ .S
    P : ∀ γ → Γ .P γ → Δ .P (S γ)
open Sub public

record Ty {i} (Γ : Con i) j : Set (i ⊔ lsuc j) where
  field
    S : Γ .S → Set j
    P : ∀ γ → Γ .P γ → S γ → Set j
    E : ∀ γ → S γ
open Ty public

record Tm {i}{j} (Γ : Con i) (A : Ty Γ j) : Set (i ⊔ j) where
  constructor tm
  field
    S : ∀ γ → A .S γ
    P : ∀ γ → (γᴾ : Γ .P γ) → A .P γ γᴾ (S γ)
open Tm public

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

p : (A : Ty Γ i) → Sub (Γ ▶ A) Γ
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

Pi : (A : Ty {i} Γ j) → Ty (Γ ▶ A) k → Ty Γ (j ⊔ k)
S (Pi A B) γ      = (x : A .S γ) → B .S (γ , x)
P (Pi A B) γ γᴾ f = (x : A .S γ)(xᴾ : A .P γ γᴾ x) → B .P (γ , x) (γᴾ , xᴾ) (f x)
E (Pi A B) γ x    = B .E (γ , x)

Pi[] : Pi {i}{Γ}{j}{k} A B [ σ ]T ≡ Pi {i}{Δ}{j}{k} (A [ σ ]T) (B [ _,ₛ_ {A = A} (σ ∘ p (A [ σ ]T) )  (q (A [ σ ]T)) ]T)
Pi[] = refl

Lam : Tm (Γ ▶ A) B → Tm Γ (Pi {i}{j = j}{k = k} A B)
S (Lam t) γ x       = t .S (γ , x)
P (Lam t) γ γᴾ x xᴾ = t .P (γ , x) (γᴾ , xᴾ)

App : Tm Γ (Pi {i}{j = j}{k = k} A B) → Tm (Γ ▶ A) B
S (App t) (γ , x)           = t .S γ x
P (App t) (γ , x) (γᴾ , xᴾ) = t .P γ γᴾ x xᴾ

Piβ : App {i}{Γ}{j}{k}{A} (Lam t) ≡ t
Piβ = refl

Piη : Lam {i}{Γ}{j}{A}{k} (App t) ≡ t
Piη = refl


-- Empty
--------------------------------------------------------------------------------

Empty : Ty {i} Γ lzero
S Empty _ = ⊤
P Empty _ _ _ = ⊥
E Empty _ = tt

Empty[] : Empty [ σ ]T ≡ Empty
Empty[] = refl

Exfalso : Tm Γ Empty → Tm Γ A
S (Exfalso {A = A} t) γ    = A .E γ
P (Exfalso {A = A} t) γ γᴾ = ⊥-elim (t .P _ γᴾ)

Exfalso[] : Exfalso {A = A} t [ σ ] ≡ Exfalso (t [ σ ])
Exfalso[] = refl


-- Nat
--------------------------------------------------------------------------------

data ℕ* : Set where
  emb : ℕ → ℕ*
  err : ℕ*

ℕ-elim : ∀ {i}(B : ℕ → Set i) → B zero → (∀ n → B n → B (suc n)) → ∀ n → B n
ℕ-elim B z s zero = z
ℕ-elim B z s (suc n) = s n (ℕ-elim B z s n)

ℕ*-elim : ∀ {i}(B : ℕ* → Set i) → (∀ n → B (emb n)) → B err → ∀ n → B n
ℕ*-elim B bemb berr (emb x) = bemb x
ℕ*-elim B bemb berr err = berr

data ℕᴾ : ℕ* → Set where
  emb : ∀ n → ℕᴾ (emb n)

ℕᴾ-elim : ∀ {i}(B : ∀ n → ℕᴾ n → Set i) → (∀ n → B _ (emb n)) → ∀ n nᴾ → B n nᴾ
ℕᴾ-elim B bemb .(emb n) (emb n) = bemb n

Nat : Ty {i} Γ lzero
S Nat _   = ℕ*
P Nat _ _ = ℕᴾ
E Nat _   = err

Nat[] : Nat [ σ ]T ≡ Nat
Nat[] = refl

Zero : Tm Γ Nat
S Zero γ    = emb zero
P Zero _ γᴾ = emb zero

Zero[] : Zero [ σ ] ≡ Zero
Zero[] = refl

Suc* : ℕ* → ℕ*
Suc* (emb x) = emb (suc x)
Suc* err = err

Sucᴾ : ∀ n → ℕᴾ n → ℕᴾ (Suc* n)
Sucᴾ .(emb n) (emb n) = emb (suc n)

Suc : Tm Γ Nat → Tm Γ Nat
S (Suc t) γ    = Suc* (t .S γ)
P (Suc t) _ γᴾ = Sucᴾ _ (P t _ γᴾ)

Suc[] : (Suc t) [ σ ] ≡ Suc (t [ σ ])
Suc[] = refl

NatElim : ∀{i j}{Γ : Con i}(B : Ty (Γ ▶ Nat) j)
          → Tm Γ (B [ id ,ₛ Zero ]T)
          → Tm (Γ ▶ Nat ▶ B) (B [ (p Nat ∘ p B) ,ₛ (Suc (q Nat [ p B ])) ]T)
          → (n : Tm Γ Nat) → Tm Γ (B [ id ,ₛ n ]T)
S (NatElim {i} {j} {Γ} B pz ps n) γ =
  ℕ*-elim (λ nSγ → B .S (γ , nSγ))
          (ℕ-elim (λ n → B .S (γ , emb n)) (pz .S γ) λ n nᴾ → ps .S ((γ , emb n) , nᴾ))
          (E B (γ , err))
          (n .S γ)
P (NatElim {i} {j} {Γ} B pz ps n) γ γᴾ =
    ℕᴾ-elim (λ nSγ nPγγᴾ →
      B .P (γ , nSγ) (γᴾ , nPγγᴾ)
            (ℕ*-elim (λ nSγ → B .S (γ , nSγ))
             (ℕ-elim (λ n₁ → B .S (γ , emb n₁)) (pz .S γ)
              (λ n₁ nᴾ → ps .S ((γ , emb n₁) , nᴾ)))
             (E B (γ , err)) (nSγ)))
      (ℕ-elim (λ n → B .P (γ , emb n) (γᴾ , emb n) (ℕ-elim (λ n₂ → B .S (γ , emb n₂))
                          (pz .S γ) (λ n₂ nᴾ → ps .S ((γ , emb n₂) , nᴾ)) n))
           (pz .P γ γᴾ)
           (λ n hyp → ps .P ((γ , emb n) ,
                              ℕ-elim (λ n₂ → B .S (γ , emb n₂)) (pz .S γ)
                              (λ n₂ nᴾ → ps .S ((γ , emb n₂) , nᴾ)) n) ((γᴾ , emb n) , hyp)))
      (n .S γ)
      (n .P γ γᴾ)

-- substitution helper, because Agda can't infer implicits inline
liftσsuc : ∀ {i' i j Δ Γ}(σ : Sub {i'}{i} Δ Γ)(B : Ty (Γ ▶ Nat) j) →
          Sub (Δ ▶ Nat ▶ B [ (σ ∘ p Nat) ,ₛ q Nat ]T) (Γ ▶ Nat ▶ B)
S (liftσsuc σ B) ((γ , n) , b) = (S σ γ , n) , b
P (liftσsuc σ B) ((γ , n) , b) ((γᴾ , nᴾ) , bᴾ) = (P σ γ γᴾ , nᴾ) , bᴾ

NatElim[] : ∀ {i' i j Δ Γ}{σ : Sub {i'}{i} Δ Γ}{B z s n}
            → NatElim {i}{j}{Γ} B z s n [ σ ]
            ≡ NatElim (B [ (σ ∘ p Nat) ,ₛ q Nat ]T) (z [ σ ]) (s [ liftσsuc σ B ]) (n [ σ ])
NatElim[] = refl

NatElimZero : ∀{i j Γ B z s} → NatElim {i}{j}{Γ} B z s Zero ≡ z
NatElimZero = refl

NatElimSuc : ∀{i j Γ B z s n}
             → NatElim {i}{j}{Γ} B z s (Suc n)
             ≡ s [ _,ₛ_ {A = B} (id ,ₛ n)  (NatElim B z s n) ]
NatElimSuc = {!refl!}


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

-- ((id ,ₛ a) ,ₛ Refl a) separately defined, because Agda can't infer implicit args.
rsub : ∀ Γ A (a : Tm {i}{j} Γ A) → Sub Γ (Γ ▶ A ▶ Id (A [ p A ]T) (a [ p A ]) (q A))
S (rsub Γ A a) γ    = (γ , a .S γ) , refl
P (rsub Γ A a) γ γᴾ = (γᴾ , a .P γ γᴾ) , refl _

-- ((id ,ₛ a') ,ₛ e) separately defined, because Agda can't infer implicit args.
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
