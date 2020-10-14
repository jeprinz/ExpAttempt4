{-# OPTIONS --cumulativity #-}
-- {-# OPTIONS --without-K --safe #-} -- idk
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive
open import Data.Empty
open import Data.Unit

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i

mutual
  data Exp : (Γ : Set i) → (Γ → Set i) → Set j where
    Lambda : {Γ : Set i} → {A : Γ → Set i} → {B : (Σ {i} {i} Γ A) → Set i} →
      Exp (Σ {i} {i} Γ A) B → Exp Γ (λ γ → ((x : A γ) → B (γ , x)))
    Π₀ : {Γ : Set i} → (A : Exp Γ (λ γ → Set₀))
      → (B : Exp (Σ {i} {i} Γ (λ γ → unq γ A)) (λ γ → Set₀))
      → Exp Γ (λ γ → Set₀)
    Π₁ : {Γ : Set i} → (A : Exp Γ (λ γ → Set₁))
      → (B : Exp (Σ {i} {i} Γ (λ γ → unq γ A)) (λ γ → Set₁))
      → Exp Γ (λ γ → Set₁)
    Π₂ : {Γ : Set i} → (A : Exp Γ (λ γ → Set₂))
      → (B : Exp (Σ {i} {i} Γ (λ γ → unq γ A)) (λ γ → Set₂))
      → Exp Γ (λ γ → Set₂)
    𝓤₀ : {Γ : Set i} → Exp Γ (λ γ → Set₁)
    𝓤₁ : {Γ : Set i} → Exp Γ (λ γ → Set₂)
    𝓤₂ : {Γ : Set i} → Exp Γ (λ γ → Set₃)
    Var : {Γ : Set i} → {T : Γ → Set i} → ((γ : Γ) → T γ)
      → Exp Γ T
    App : {Γ : Set i} → {A : Γ → Set i} → {B : Σ {i} {i} Γ A → Set i} →
        Exp Γ (λ γ → (a : A γ) → B (γ , a)) → (x : Exp Γ A) → Exp Γ (λ γ → B (γ , unq γ x))
        -- TODO: compare this definition of App with old

  -- unquote
-- TODO : should move γ arg to end
  unq : {Γ : Set i} → (γ : Γ) → {T : Γ → Set i} → Exp Γ T → T γ
  unq γ (Lambda e) = λ x → unq (γ , x) e
  unq γ (Var f) = f γ
  unq γ (App e₁ e₂) = (unq γ e₁) (unq γ e₂)
  unq γ (Π₀ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ (Π₁ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ (Π₂ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ 𝓤₀ = Set₀
  unq γ 𝓤₁ = Set₁
  unq γ 𝓤₂ = Set₂

idE : Exp ⊤ (λ γ → (T : Set₀) → T → T)
idE = Lambda (Lambda (Var (λ (_ , γ) → γ ) ) ) -- λ T t . t

-- of course, this implementation of Var allows you to just embed programs in expressions
stupid : Exp ⊤ (λ γ → (T : Set₀) → T → T)
stupid = Var (λ γ T t → t)

-- TODO: any way that I can make Exp parametrized by just a single T instead of Γ and T?

sub : {Γ Γ' : Set i} → {T : Γ → Set i} → (ϕ : Γ' → Γ) → Exp Γ T → Exp Γ' (λ γ → T (ϕ γ))
sub {Γ} {Γ'} ϕ (Lambda {_} {A} {B} e)
  = let x = sub {Σ Γ A} {Σ Γ' (λ γ → A (ϕ γ))} (λ (γ , a) → (ϕ γ) , a ) e in {!x!}
sub ϕ (Π₀ e e₁) = {!   !}
sub ϕ (Π₁ e e₁) = {!   !}
sub ϕ (Π₂ e e₁) = {!   !}
sub ϕ 𝓤₀ = {!   !}
sub ϕ 𝓤₁ = {!   !}
sub ϕ 𝓤₂ = {!   !}
sub ϕ (Var x) = {!   !}
sub ϕ (App e e₁) = {!   !}


{-
IDEA:
What I really want is for if Γ is a prefix of Γ',
then (Γ → Set i) is a subtype of (Γ' → Set i)

or (ctxType Γ → Set i) subtype of (ctxType Γ' → Set i)


Imagine a type theory with (A × B → C) subtype of (A → C)

-}
