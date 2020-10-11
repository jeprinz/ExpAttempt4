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

mutual
  data Exp : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    Lambda : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
      Exp (Γ , A) B → Exp Γ (λ γ → ((x : A γ) → B (γ , x)))
    WeakerCtx : {Γ : Context} → {new t : ctxType Γ → Set i} →
      Exp Γ t → Exp (Γ , new) (λ {(rest , _) → t rest})
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
    InCtx : {Γ : Context} → {t : ctxType Γ → Set i} → Exp (Γ , t) (λ {(rest , _) → t rest})
    App : {Γ : Context} → {A : ctxType Γ → Set i} → {B : (γ : ctxType Γ) → A γ → Set i} →
      Exp Γ (λ γ → (a : A γ) → B γ a) → (x : Exp Γ A) → Exp Γ (λ γ → B γ (unq γ x))

  -- unquote
  unq : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → Exp Γ T → T γ
  unq γ (Lambda e) = λ x → unq (γ , x) e
  unq γ (WeakerCtx e) = unq (proj₁ γ) e
  unq γ InCtx = proj₂ γ
  unq γ (App e₁ e₂) = (unq γ e₁) (unq γ e₂)
  unq γ (Π₀ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ (Π₁ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ (Π₂ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ 𝓤₀ = Set₀
  unq γ 𝓤₁ = Set₁
  unq γ 𝓤₂ = Set₂

id : Exp ∅ (λ γ → (T : Set₀) → T → T)
id = Lambda (Lambda InCtx) -- λ T t . t

-- Think: why are substitution and weakening hard/neccesary?
-- Why will they become harder if I make WeakerCtx a function instead of constructor?

f1 : Exp ∅ (λ γ → (A B : Set₀) → (A → B) → A → B)
f1 = Lambda (Lambda (Lambda (Lambda (App (WeakerCtx InCtx) InCtx ))))
-- λ A B f x . f x

-----------------------------------------------------------------------------

mutual
  data Value : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    Lambda : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
      Value (Γ , A) B → Value Γ (λ γ → ((x : A γ) → B (γ , x)))
    WeakerCtx : {Γ : Context} → {new t : ctxType Γ → Set i} →
      Value Γ t → Value (Γ , new) (λ {(rest , _) → t rest})
    Π₀ : {Γ : Context} → (A : Value Γ (λ γ → Set₀))
      → (B : Value (Γ , (λ γ → unqv γ A)) (λ γ → Set₀))
      → Value Γ (λ γ → Set₀)
    Π₁ : {Γ : Context} → (A : Value Γ (λ γ → Set₁))
      → (B : Value (Γ , (λ γ → unqv γ A)) (λ γ → Set₁))
      → Value Γ (λ γ → Set₁)
    Π₂ : {Γ : Context} → (A : Value Γ (λ γ → Set₂))
      → (B : Value (Γ , (λ γ → unqv γ A)) (λ γ → Set₂))
      → Value Γ (λ γ → Set₂)
    𝓤₀ : {Γ : Context} → Value Γ (λ γ → Set₁)
    𝓤₁ : {Γ : Context} → Value Γ (λ γ → Set₂)
    𝓤₂ : {Γ : Context} → Value Γ (λ γ → Set₃)
    FromU : ∀{Γ} → ∀{T} → Ualue Γ T → Value Γ T

  data Ualue : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    InCtx : {Γ : Context} → {t : ctxType Γ → Set i} → Ualue (Γ , t) (λ {(rest , _) → t rest})
    App : {Γ : Context} → {A : ctxType Γ → Set i} → {B : (γ : ctxType Γ) → A γ → Set i} →
      Ualue Γ (λ γ → (a : A γ) → B γ a) → (x : Value Γ A) → Ualue Γ (λ γ → B γ (unqv γ x))

  -- TODO: define unqv and unqu by first converting the values back to Exp and then using unq.
  injv : ∀{Γ T} → Value Γ T → Exp Γ T
  injv = ?
  inju : ∀{Γ T} → Ualue Γ T → Exp Γ T
  inju = ?

  -- unquote
  unqv : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → Value Γ T → T γ
  unqv γ (Lambda e) = λ x → unqv (γ , x) e
  unqv γ (WeakerCtx e) = unqv (proj₁ γ) e
  unqv γ (Π₀ A B) = (a : unqv γ A) → (unqv (γ , a) B)
  unqv γ (Π₁ A B) = (a : unqv γ A) → (unqv (γ , a) B)
  unqv γ (Π₂ A B) = (a : unqv γ A) → (unqv (γ , a) B)
  unqv γ 𝓤₀ = Set₀
  unqv γ 𝓤₁ = Set₁
  unqv γ 𝓤₂ = Set₂
  unqv γ (FromU u) = unqu γ u

  unqu : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → Ualue Γ T → T γ
  unqu γ InCtx = proj₂ γ
  unqu γ (App e₁ e₂) = (unqu γ e₁) (unqv γ e₂)

eval : ∀{Γ T} → Exp Γ T → Value Γ T
eval (Lambda e) = Lambda (eval e)
eval (WeakerCtx e) = WeakerCtx (eval e)
eval (Π₀ e e₁) = Π₀ (eval e) {!   !}
eval (Π₁ e e₁) = Π₁ (eval e) {!   !}
eval (Π₂ e e₁) = Π₂ (eval e) {!   !}
eval 𝓤₀ = 𝓤₀
eval 𝓤₁ = 𝓤₁
eval 𝓤₂ = 𝓤₂
eval InCtx = FromU InCtx
eval (App e e₁) = {!   !}
-- The above could be, if not for termination:
-- let v = (eval e), v₁ = (eval e₁)
-- prove that v is a Lambda x
-- convert v to Exp, substitute v₁ in for x (in Exp, substitution is trivial, no computation)
-- eval the final result

-- The big question: is it possible to do the above in a TERMINATING way with girard's method???
