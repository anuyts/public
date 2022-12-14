{-# OPTIONS --guarded #-}
module LaterPrimsMLTT where

-- typechecks in Agda version 2.6.4-2f0ea06
{- Based on this file by Saizan:
   https://github.com/agda/agda/blob/master/test/Succeed/LaterPrims.agda
-}

open import Agda.Primitive

open import Data.Nat
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

private
  variable
    l : Level
    A B : Set l

-- We postulate Tick as it is supposed to be an abstract sort.
postulate
  Tick : LockU

▹_ : ∀ {l} → Set l → Set l
▹_ A = (@tick x : Tick) -> A

▸_ : ∀ {l} → ▹ Set l → Set l
▸ A = (@tick x : Tick) → A x

next : A → ▹ A
next x _ = x

_⊛_ : ▹ (A → B) → ▹ A → ▹ B
_⊛_ f x a = f a (x a)

map▹ : (f : A → B) → ▹ A → ▹ B
map▹ f x α = f (x α)

ap : ∀ {A B : Set} (f : A → B) → ∀ {x y} → x ≡ y → f x ≡ f y
ap = cong

_$>_ : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ x → f x ≡ g x
_$>_ = cong-app

postulate
  fix : ∀ {l} {A : Set l} → (▹ A → A) → A
  efix : ∀ {l} {A : Set l} → (f : ▹ A → A) → fix f ≡ f (next (fix f))
  later-ext : ∀ {l} {A : Set l} → {f g : ▹ A} → (▸ \ α → f α ≡ g α) → f ≡ g

cong-tick : ∀ {l} {A : Set l} {a b : ▹ A} → a ≡ b → ▸ λ α → a α ≡ b α
cong-tick refl α = refl

data gStream (A : Set) : Set where
  cons : (x : A) (xs : ▹ gStream A) → gStream A

repeat : ∀ {A : Set} → A → gStream A
repeat a = fix \ repeat▹ → cons a repeat▹

repeat-eq : ∀ {A : Set} (a : A) → repeat a ≡ cons a (\ α → repeat a)
repeat-eq a = efix (cons a)

map : ∀ {A B : Set} → (A → B) → gStream A → gStream B
map f = fix \ map▹ → \ { (cons a as) → cons (f a) \ α → map▹ α (as α) }

map-eq : ∀ {A B : Set} → (f : A → B) → ∀ a as → map f (cons a as) ≡ cons (f a) (\ α → map f (as α))
map-eq f a b = cong-app (efix _) (cons a b)

_∙_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ = trans

map-repeat : ∀ {A B : Set} → (a : A) → (f : A → B) → map f (repeat a) ≡ repeat (f a)
map-repeat a f = fix λ ihyp → begin
  map f (repeat a)
    ≡⟨ cong (map f) (repeat-eq a) ⟩
  map f (cons a (next (repeat a)))
    ≡⟨ map-eq f a (next (repeat a)) ⟩
  cons (f a) (next (map f (repeat a)))
    ≡⟨ cong (cons (f a)) (later-ext ihyp) ⟩
  cons (f a) (next (fix (cons (f a))))
    ≡⟨ sym (efix (cons (f a))) ⟩
  fix (cons (f a)) ∎

tail : ∀ {A : Set} → gStream A → ▹ gStream A
tail (cons x xs) = xs

-- If fuel = 20, then these operations unfold 20 times before getting stuck.

module FlexFuel where
  fix-fuel' : (fuel : ℕ) → ∀ {l} {A : Set l} → (▹ A → A) → A
  fix-fuel' zero f = fix f
  fix-fuel' (suc fuel) f = f (next (fix-fuel' fuel f))

  efix-fuel' : (fuel : ℕ) → ∀ {l} {A : Set l} → (f : ▹ A → A) → fix-fuel' fuel f ≡ f (next (fix-fuel' fuel f))
  efix-fuel' zero f = efix f
  efix-fuel' (suc fuel) f = cong f (cong next (efix-fuel' fuel f))

  fix-ignore-fuel' : (fuel : ℕ) → ∀ {l} {A : Set l} → (f : ▹ A → A) → fix-fuel' fuel f ≡ fix f
  fix-ignore-fuel' zero f = refl
  fix-ignore-fuel' (suc fuel) f = begin
    fix-fuel' (suc fuel) f
      ≡⟨ cong f (cong next (fix-ignore-fuel' fuel f)) ⟩
    f (next (fix f))
      ≡⟨ sym (efix f) ⟩
    fix f ∎

module GlobalFuel (fuel : ℕ) where
  open FlexFuel
  
  fix-fuel = fix-fuel' fuel
  efix-fuel = efix-fuel' fuel
  fix-ignore-fuel = fix-ignore-fuel' fuel
