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

mutual
  data Context : ∀{l} → Set l where
    ∅ : Context
    ConsCtx : ∀{i j} → (ctx : Context i) → (ctxType ctx → Set j) → Context (i ⊔ j)

  -- outputs a type representing the information contained in the context
  ctxType : Context → Setω
  ctxType ∅ = ⊤
  ctxType (ConsCtx ctx h) = Σ (ctxType ctx) (λ t → h t)

mutual
  data Exp : ∀{l} → (Γ : Context) → (ctxType Γ → Set l) → Setω where
    𝓤 : ∀{l} → {Γ : Context} → Exp (lsuc l) Γ (λ γ → Set l)

  -- eval : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → Exp Γ T → T γ
  -- eval γ (Lambda e) = λ x → eval (γ , x) e
  -- eval γ (WeakerCtx e) = eval (proj₁ γ) e
  -- eval γ InCtx = proj₂ γ
  -- eval γ (App e₁ e₂) = (eval γ e₁) (eval γ e₂)

  -- IDEA: using core types, why can't I do girards's method and define eval?
  -- also why can't constructors like lambda have their type parametrized by Exp U,
  -- and then use eval to get it to the core types (does that have any advantages?)

  -- TODO: big question here to make this at all useful would be can I get the
  -- type Level_n in Agda?
