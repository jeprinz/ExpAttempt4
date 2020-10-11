open import Data.Nat
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive

data Fin : ℕ → Set where
  Z : ∀{n} → Fin n
  S : ∀{n} → Fin n → Fin (suc n)

asLevel : ℕ → Level
asLevel 0 = lzero
asLevel (suc n) = lsuc (asLevel n)

fasLevel : ∀{n} → Fin n → Level
fasLevel Z = lzero
fasLevel (S n) = lsuc (fasLevel n)

data ⊤ {i : Level} : Set i where
  tt : ⊤

-- The maximum type level for represented programs
n : ℕ
n = 10

ExpLevel = Fin n

predpredi = asLevel n
predi = lsuc predpredi
i = lsuc predi
j = lsuc i
mutual
  data Context : Set j where
    ∅ : Context
    ConsCtx : (ctx : Context) → (l : ExpLevel) → (ctxType ctx → Set (fasLevel l)) → Context

  -- outputs a type representing the information contained in the context
  ctxType : Context → Set j
  ctxType ∅ = ⊤
  ctxType (ConsCtx ctx _ h) = Σ (ctxType ctx) (λ t → h t)

mutual
  data Exp : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    InCtx : {Γ : Context} → {l : ExpLevel} → {t : ctxType Γ → Set (fasLevel l)}
      → Exp (ConsCtx Γ l t) (λ {(rest , _) → t rest})
    Lambda : {Γ : Context} → {la lb : ExpLevel}
      → {A : ctxType Γ → Set (fasLevel la)} → {B : ctxType (ConsCtx Γ la A) → Set (fasLevel lb)} →
      Exp (ConsCtx Γ la A) B → Exp Γ (λ γ → ((x : A γ) → B (γ , x)))
    WeakerCtx : {Γ : Context} → {l : ExpLevel} → {new t : ctxType Γ → Set (fasLevel l)} →
      Exp Γ t → Exp (ConsCtx Γ l new) (λ {(rest , _) → t rest})
    App : {Γ : Context} → {A : ctxType Γ → Set i} → {B : (γ : ctxType Γ) → A γ → Set i} →
      Exp Γ (λ γ → (a : A γ) → B γ a) → (x : Exp Γ A) → Exp Γ (λ γ → B γ (eval γ x))
    𝓤 : {Γ : Context} → Exp Γ (λ γ → Set predi)
    Π : {Γ : Context} → (A : ctxType Γ → Set predi) → (B : (γ : ctxType Γ) → A γ → Set predi) →
      Exp Γ (λ γ → Set predi)

  eval : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → Exp Γ T → T γ
  eval γ InCtx = proj₂ γ
  eval γ (Lambda e) = λ x → eval (γ , x) e
  eval γ (WeakerCtx e) = eval (proj₁ γ) e
  eval γ (App e₁ e₂) = (eval γ e₁) (eval γ e₂)
  eval γ 𝓤 = Set predpredi
  eval γ (Π A B) = (a : A γ) → B γ a
