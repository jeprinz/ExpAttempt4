open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive
open import Data.Empty

data ⊤ {i : Level} : Set i where
  tt : ⊤

predpredi = lzero
predi = lsuc predpredi
i = lsuc predi
j = lsuc i
mutual
  data Context : Set j where
    ∅ : Context
    ConsCtx : (ctx : Context) → (ctxType ctx → Set i) → Context

  -- outputs a type representing the information contained in the context
  ctxType : Context → Set j
  ctxType ∅ = ⊤
  ctxType (ConsCtx ctx h) = Σ (ctxType ctx) (λ t → h t)

mutual
  data Value : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    Lambda : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (ConsCtx Γ A) → Set i} →
      Value (ConsCtx Γ A) B → Value Γ (λ γ → ((x : A γ) → B (γ , x)))
    WeakerCtx : {Γ : Context} → {new t : ctxType Γ → Set i} →
      Value Γ t → Value (ConsCtx Γ new) (λ {(rest , _) → t rest})
    -- 𝓤 : {Γ : Context} → Value Γ (λ γ → Set predi)
    -- Π : {Γ : Context} → (A : ctxType Γ → Set predi) → (B : (γ : ctxType Γ) → A γ → Set predi) →
    --   Value Γ (λ γ → Set predi)
    fromU : ∀{Γ} → ∀{T} → Ualue Γ T → Value Γ T

  data Ualue : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    InCtx : {Γ : Context} → {t : ctxType Γ → Set i} → Ualue (ConsCtx Γ t) (λ {(rest , _) → t rest})
    App : {Γ : Context} → {A : ctxType Γ → Set i} → {B : (γ : ctxType Γ) → A γ → Set i} →
      Ualue Γ (λ γ → (a : A γ) → B γ a) → (x : Value Γ A) → Ualue Γ (λ γ → B γ (eval γ x))

  eval : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → Value Γ T → T γ
  eval γ (Lambda e) = λ x → eval (γ , x) e
  eval γ (WeakerCtx e) = eval (proj₁ γ) e
  eval γ (fromU u) = evalU γ u

  evalU : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → Ualue Γ T → T γ
  evalU γ InCtx = proj₂ γ
  evalU γ (App e₁ e₂) = (evalU γ e₁) (eval γ e₂)

fact : ∀{A B} → Value ∅ (λ γ → A → B) → Value (ConsCtx ∅ (λ γ → A)) (λ γ → B)
fact v = {!   !}

code : Context → Set
code ∅ = ⊥
code (ConsCtx g x) = ⊤

ap : ∀{l} → {A B : Set l} → ∀{x y} → (f : A → B) → x ≡ y → (f x) ≡ (f y)
ap f refl = refl

transport : ∀{l k} → {A : Set l} → ∀{x y} → (f : A → Set k)
  → x ≡ y → (f x) → (f y)
transport f refl x = x

nonEmpty : ∀{Γ T} → Ualue Γ T → ¬(Γ ≡ ∅)
nonEmpty InCtx = λ p → (transport code p tt)
nonEmpty (App u x) = nonEmpty u

-- An alternate way of doing this where A and B are functions rather than types:
-- factImpl : ∀{Γ T} → Value Γ T → (pΓ : Γ ≡ ∅) → (A : ctxType ∅ → Set i) → (B : ctxType (ConsCtx ∅ A) → Set i)
--   → (T ≡ (λ γ → let γ' = transport (λ Γ → ctxType Γ) pΓ γ in (a : A γ') → B (γ' , a)))
--     → Value (ConsCtx ∅ A) B
-- unfortunately, A₁ → B₁ ≡ A → B does not imply that A₁ ≡ A and B₁ ≡ B (wait maybe it does)


factImpl : ∀{Γ T} → Value Γ T → (Γ ≡ ∅) → (A B : Set i)
  → (T ≡ (λ γ → A → B)) → Value (ConsCtx ∅ (λ γ → A)) (λ γ → B)
-- replace above with dependent tuple (A : Set i, B : Set i, T ≡ λ γ → (a : A γ) → B (γ , a), Value (ConsCtx ∅ A) B)
factImpl {Γ} {T} (Lambda e) pΓ A B pT = {!   !}
factImpl (fromU u) pΓ = ⊥-elim (nonEmpty u pΓ) -- contradiction, can't happen

fact' : ∀(A) → ∀(B) → Value ∅ (λ γ → A → B) → Value (ConsCtx ∅ (λ γ → A)) (λ γ → B)
fact' A B v = factImpl v refl A B refl
