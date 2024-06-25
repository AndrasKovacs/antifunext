{-# OPTIONS --without-K #-}

module Lib where

open import Relation.Binary.PropositionalEquality
  renaming (subst to tr; sym to infix 5 _⁻¹; trans to infixr 4 _◼_; cong to ap)
  hiding ([_])
  public
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂) public
open import Data.Nat   hiding (_≟_; _⊔_) public
open import Data.Unit  public
open import Data.Empty public
open import Data.Sum hiding (assocʳ; assocˡ; map; map₁; map₂; swap) public
