{-# OPTIONS --cumulativity #-}
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
  data Context : Set j where
    ∅ : Context
    _,_ : (ctx : Context) → (ctxType ctx → Set i) → Context

  -- outputs a type representing the information contained in the context
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

idE : Exp ∅ (λ γ → (T : Set₀) → T → T)
idE = Lambda (Lambda (Var same)) -- λ T t . t

proofSame : unq tt idE ≡ (λ T t → t)
proofSame = refl

-- Think: why are substitution and weakening hard/neccesary?

f1 : Exp ∅ (λ γ → (A B : Set₀) → (A → B) → A → B)
f1 = Lambda (Lambda (Lambda (Lambda (App (Var (next same)) (Var same)))))
-- λ A B f x . f x

------------------------------------------------------------------------
------------------------------------------------------------------------
