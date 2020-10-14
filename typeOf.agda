{-# OPTIONS --cumulativity #-}
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive
open import Data.Empty
open import Data.Unit

module typeOf where

baseLevel = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
i = lsuc baseLevel
j = lsuc i

mutual
  data Context : Set j where
    ∅ : Context
    _,_ : (ctx : Context) → (ctxType ctx → Set i) → Context

  ctxType : Context → Set j
  ctxType ∅ = ⊤
  ctxType (ctx , h) = Σ (ctxType ctx) (λ t → h t)

  data InCtx : Context → Set j where
    same : ∀{Γ T} → InCtx (Γ , T)
    next : ∀{Γ T} → InCtx Γ → InCtx (Γ , T)

  CtxAt : ∀{Γ} → InCtx Γ → Context
  CtxAt {(Γ , _)} same = Γ
  CtxAt {(_ , _)} (next icx) = CtxAt icx

  TypeAt : ∀{Γ} → (icx : InCtx Γ) → (ctxType Γ → Set i)
  TypeAt {(_ , T)} same (γ , _) = T γ
  TypeAt {.(_ , _)} (next icx) (γ , _) = TypeAt icx γ

  proj : ∀{Γ} → (icx : InCtx Γ) → (γ : ctxType Γ) → TypeAt icx γ
  proj same (γ , t) = t
  proj (next icx) (γ , _) = proj icx γ

module Exp1 where
  mutual
    data Exp : (Γ : Context) → (ctxType Γ → Set i) → Set j where
      Lambda : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
        Exp (Γ , A) B → Exp Γ (λ γ → ((x : A γ) → B (γ , x)))
      Π₀ : {Γ : Context} → (A : Exp Γ (λ γ → Set₀))
        → (B : Exp (Γ , (λ γ → unq γ A)) (λ γ → Set₀))
        → Exp Γ (λ γ → Set₀)
      Π₁ : {Γ : Context} → (A : Exp Γ (λ γ → Set₁))
        → (B : Exp (Γ , (λ γ → unq γ A)) (λ γ → Set₁))
        → Exp Γ (λ γ → Set₁)
      Π₂ : {Γ : Context} → (A : Exp Γ (λ γ → Set₂))
        → (B : Exp (Γ , (λ γ → unq γ A)) (λ γ → Set₂))
        → Exp Γ (λ γ → Set₂)
      𝓤₀ : {Γ : Context} → Exp Γ (λ γ → Set₁)
      𝓤₁ : {Γ : Context} → Exp Γ (λ γ → Set₂)
      𝓤₂ : {Γ : Context} → Exp Γ (λ γ → Set₃)
      Var : ∀{Γ} → (icx : InCtx Γ)
        → Exp Γ (λ γ → TypeAt icx γ)
      App : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
          Exp Γ (λ γ → (a : A γ) → B (γ , a)) → (x : Exp Γ A) → Exp Γ (λ γ → B (γ , unq γ x))
          -- TODO: compare this definition of App with old

    -- unquote
  -- TODO : should move γ arg to end
    unq : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → Exp Γ T → T γ
    unq γ (Lambda e) = λ x → unq (γ , x) e
    unq γ (Var icx) = proj icx γ
    unq γ (App e₁ e₂) = (unq γ e₁) (unq γ e₂)
    unq γ (Π₀ A B) = (a : unq γ A) → (unq (γ , a) B)
    unq γ (Π₁ A B) = (a : unq γ A) → (unq (γ , a) B)
    unq γ (Π₂ A B) = (a : unq γ A) → (unq (γ , a) B)
    unq γ 𝓤₀ = Set₀
    unq γ 𝓤₁ = Set₁
    unq γ 𝓤₂ = Set₂


module Exp2 where
  mutual
    data Exp : (Γ : Context) → (ctxType Γ → Set i) → Set j where
      Lambda : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
        Exp (Γ , A) B → Exp Γ (λ γ → ((x : A γ) → B (γ , x)))
      Π₀ : {Γ : Context} → (A : Exp Γ (λ γ → Set₀))
        → (B : Exp (Γ , (λ γ → unq γ A)) (λ γ → Set₀))
        → Exp Γ (λ γ → Set₀)
      Π₁ : {Γ : Context} → (A : Exp Γ (λ γ → Set₁))
        → (B : Exp (Γ , (λ γ → unq γ A)) (λ γ → Set₁))
        → Exp Γ (λ γ → Set₁)
      Π₂ : {Γ : Context} → (A : Exp Γ (λ γ → Set₂))
        → (B : Exp (Γ , (λ γ → unq γ A)) (λ γ → Set₂))
        → Exp Γ (λ γ → Set₂)
      𝓤₀ : {Γ : Context} → Exp Γ (λ γ → Set₁)
      𝓤₁ : {Γ : Context} → Exp Γ (λ γ → Set₂)
      𝓤₂ : {Γ : Context} → Exp Γ (λ γ → Set₃)
      𝓤₃ : {Γ : Context} → Exp Γ (λ γ → Set₄)
      Var : ∀{Γ} → (icx : InCtx Γ)
        → Exp Γ (λ γ → TypeAt icx γ)
      App : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
          Exp Γ (λ γ → (a : A γ) → B (γ , a)) → (x : Exp Γ A) → Exp Γ (λ γ → B (γ , unq γ x))
      Lift₀ : ∀{Γ} → Exp Γ (λ γ → Set₀) → Exp Γ (λ γ → Set baseLevel)
      Lift₁ : ∀{Γ} → Exp Γ (λ γ → Set₁) → Exp Γ (λ γ → Set baseLevel)
      Lift₂ : ∀{Γ} → Exp Γ (λ γ → Set₂) → Exp Γ (λ γ → Set baseLevel)
      Lift₃ : ∀{Γ} → Exp Γ (λ γ → Set₃) → Exp Γ (λ γ → Set baseLevel)
      Lift₄ : ∀{Γ} → Exp Γ (λ γ → Set₄) → Exp Γ (λ γ → Set baseLevel)

    -- unquote
  -- TODO : should move γ arg to end
    unq : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → Exp Γ T → T γ
    unq γ (Lambda e) = λ x → unq (γ , x) e
    unq γ (Var icx) = proj icx γ
    unq γ (App e₁ e₂) = (unq γ e₁) (unq γ e₂)
    unq γ (Π₀ A B) = (a : unq γ A) → (unq (γ , a) B)
    unq γ (Π₁ A B) = (a : unq γ A) → (unq (γ , a) B)
    unq γ (Π₂ A B) = (a : unq γ A) → (unq (γ , a) B)
    unq γ 𝓤₀ = Set₀
    unq γ 𝓤₁ = Set₁
    unq γ 𝓤₂ = Set₂
    unq γ 𝓤₃ = Set₃
    unq γ (Lift₀ e) = unq γ e
    unq γ (Lift₁ e) = unq γ e
    unq γ (Lift₂ e) = unq γ e
    unq γ (Lift₃ e) = unq γ e
    unq γ (Lift₄ e) = unq γ e

test : Exp1.Exp ∅ (λ γ → (T : Set₀) → T → T)
test = Exp1.Lambda (Exp1.Lambda (Exp1.Var same))

typeOf : ∀{Γ T} → Exp1.Exp Γ T → Exp2.Exp Γ (λ γ → Set baseLevel)
typeOf (Exp1.Lambda e) = {!   !}
typeOf (Exp1.Π₀ e e₁) = {!   !}
typeOf (Exp1.Π₁ e e₁) = {!   !}
typeOf (Exp1.Π₂ e e₁) = {!   !}
typeOf Exp1.𝓤₀ = Exp2.Lift₂ Exp2.𝓤₁
typeOf Exp1.𝓤₁ = Exp2.Lift₃ Exp2.𝓤₂
typeOf Exp1.𝓤₂ = Exp2.Lift₄ Exp2.𝓤₃
typeOf (Exp1.Var icx) = {!   !}
typeOf (Exp1.App e e₁) = {!   !}

-- Maybe instead of typeOf, we can do something like:

data FreeTheorem : Set i → Set i where
  -- arrow : ∀{A B} → (x x' : A) → 
