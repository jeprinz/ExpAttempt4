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
    -- This is full dependent Lambda, and that works
    Lambda : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
      Exp (Γ , A) B → Exp Γ (λ γ → ((x : A γ) → B (γ , x)))
    _⇒₀_ : {Γ : Context} → (A B : Exp Γ (λ γ → Set₀))
      → Exp Γ (λ γ → Set₀)
    _⇒₁_ : {Γ : Context} → (A B : Exp Γ (λ γ → Set₀))
      → Exp Γ (λ γ → Set₀)
    _⇒₂_ : {Γ : Context} → (A B : Exp Γ (λ γ → Set₀))
      → Exp Γ (λ γ → Set₀)
    𝓤₀ : {Γ : Context} → Exp Γ (λ γ → Set₁)
    𝓤₁ : {Γ : Context} → Exp Γ (λ γ → Set₂)
    𝓤₂ : {Γ : Context} → Exp Γ (λ γ → Set₃)
    Var : ∀{Γ} → (icx : InCtx Γ)
      → Exp Γ (λ γ → TypeAt icx γ)
    App : {Γ : Context} → {A B : ctxType Γ → Set i} →
        Exp Γ (λ γ → A γ → B γ) → (x : Exp Γ A) → Exp Γ (λ γ → B γ)
    AppT₀ : {Γ : Context} → {B : ctxType Γ → Set i} →
        Exp Γ (λ γ → Set₀ → B γ) → Exp Γ (λ γ → Set₀) → Exp Γ B

  -- unquote
-- TODO : should move γ arg to end
  unq : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → Exp Γ T → T γ
  unq γ (Lambda e) = λ x → unq (γ , x) e
  unq γ (Var icx) = proj icx γ
  unq γ (App e₁ e₂) = (unq γ e₁) (unq γ e₂)
  unq γ (AppT₀ e₁ e₂) = (unq γ e₁) (unq γ e₂)
  unq γ (A ⇒₀ B) = (unq γ A) → (unq γ B)
  unq γ (A ⇒₁ B) = (unq γ A) → (unq γ B)
  unq γ (A ⇒₂ B) = (unq γ A) → (unq γ B)
  unq γ 𝓤₀ = Set₀
  unq γ 𝓤₁ = Set₁
  unq γ 𝓤₂ = Set₂

idE : Exp ∅ (λ γ → (T : Set₀) → T → T)
idE = Lambda (Lambda (Var same)) -- λ T t . t

proofSame : unq tt idE ≡ (λ T t → t)
proofSame = refl

idE' : ∀{Γ} → Exp Γ (λ γ → (T : Set₀) → T → T)
idE' = Lambda (Lambda (Var same)) -- λ T t . t

f1 : Exp ∅ (λ γ → (A B : Set₀) → (A → B) → A → B)
f1 = Lambda (Lambda (Lambda (Lambda (App (Var (next same)) (Var same)))))
-- λ A B f x . f x

------------------------------------------------------------------------
------------------------------------------------------------------------


TypeAt' : ∀{Γ} → (icx : InCtx Γ) → (ctxType (CtxAt icx) → Set i)
TypeAt' {(_ , T)} same = T
TypeAt' (next icx) = TypeAt' icx


mutual
  -- Substitution
  subΓ : ∀{Γ} → (icx : InCtx Γ) → Exp (CtxAt icx) (TypeAt' icx) → Context
  subΓ {(Γ , _)} same e = Γ
  subΓ {(_ , T)} (next icx) e = (subΓ icx e , λ γ → T (subγ icx e γ))
  -- subΓ {(_ , T)} (next icx) e = (subΓ icx e , λ γ → {!   !} )

  subγ : ∀{Γ} → (icx : InCtx Γ) → (e : Exp (CtxAt icx) (TypeAt' icx))
    → ctxType (subΓ icx e) → ctxType Γ
  subγ same e γ = (γ , unq γ e)
  subγ (next icx) e (γ , t) = (subγ icx e γ , t)

subT : ∀{Γ} → (icx : InCtx Γ) → (e : Exp (CtxAt icx) (TypeAt' icx))
  → (ctxType Γ → Set i) → (ctxType (subΓ icx e) → Set i)
subT icx e T = λ γ → T (subγ icx e γ)
  -- subT same e T γ =  T (γ , unq γ e)
  -- subT (next icx) e T = {!   !}

data Pre : Context → Set j where
  same : ∀{Γ} → Pre Γ
  next : ∀{Γ T} → Pre Γ → Pre (Γ , T)

preCtxAt : ∀{Γ} → Pre Γ → Context
preCtxAt (same {Γ}) = Γ
preCtxAt (next pre) = preCtxAt pre

-- TODO: dang, this is going to be just as hard as always...

weakenExp : ∀{Γ A} → (pre : Pre Γ) → (T : preCtxAt pre → Set i)
  → Exp Γ T → Exp (Γ , A) (λ γ → T (proj₁ γ))
weakenExp = {!   !}

subExp : ∀{Γ T} → (icx : InCtx Γ) → (e : Exp (CtxAt icx) (TypeAt' icx))
  → Exp Γ T → Exp (subΓ icx e) (subT icx e T)

-- TODO: will need to prove that substitution commutes with unquoting
subExp icx toSub (Lambda e) = Lambda (subExp (next icx) toSub e)
subExp icx toSub (A ⇒₀ B) = (subExp icx toSub A) ⇒₀ (subExp icx toSub B)
subExp icx toSub (A ⇒₁ B) = (subExp icx toSub A) ⇒₁ (subExp icx toSub B)
subExp icx toSub (A ⇒₂ B) = (subExp icx toSub A) ⇒₂ (subExp icx toSub B)
subExp icx toSub 𝓤₀ = 𝓤₀
subExp icx toSub 𝓤₁ = 𝓤₁
subExp icx toSub 𝓤₂ = 𝓤₂
  -- TODO: extract these four cases into a function about InCtx
subExp same toSub (Var same) = toSub
subExp same toSub (Var (next icx₁)) = Var icx₁
subExp (next icx) toSub (Var same) = Var same
subExp (next icx) toSub (Var (next icx₁)) = let x = subExp icx toSub (Var icx₁) in {!   !}
subExp icx toSub (App e₁ e₂) = App (subExp icx toSub e₁) (subExp icx toSub e₂)
subExp icx toSub (AppT₀ e₁ e₂) = AppT₀ (subExp icx toSub e₁) (subExp icx toSub e₂)
    -- in App {subΓ icx toSub} {subT icx toSub A} {subT (next icx) toSub B}
      -- x {!   !}


-- IDEA: TODO: why can't I do this exact program but contexts use a defined
-- type instead of built in types? But like they're still functions ctxType Γ → DefinedType


data _↦_ : ∀{Γ T} → Exp Γ T → Exp Γ T → Set j where
  APP : {Γ : Context} → {A B : ctxType Γ → Set i} →
      (e e' : Exp Γ (λ γ → A γ → B γ)) → e ↦ e'
      → (e₂ : Exp Γ A) → App e e₂ ↦ App e' e₂
